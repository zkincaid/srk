open Syntax
open Linear
open BatPervasives

include Log.Make(struct let name = "srk.quantifier" end)

exception Equal_term of Linear.QQVector.t
 
module V = Linear.QQVector
module VS = BatSet.Make(Linear.QQVector)
module VM = BatMap.Make(Linear.QQVector)
module ZZVector = Linear.ZZVector
module IntSet = SrkUtil.Int.Set

let substitute_const srk sigma expr =
  let simplify t = of_linterm srk (linterm_of srk t) in
  rewrite srk ~up:(fun expr ->
      match Expr.refine srk expr with
      | `Formula phi ->
        begin
          try
            match Formula.destruct srk phi with
            | `Atom (`Arith (`Eq, s, t)) ->
              (mk_eq srk (simplify s) (simplify t) :> ('a, typ_fo) expr)
            | `Atom (`Arith (`Leq, s, t)) ->
              (mk_leq srk (simplify s) (simplify t) :> ('a, typ_fo) expr)
            | `Atom (`Arith (`Lt, s, t)) ->
              (mk_lt srk (simplify s) (simplify t) :> ('a, typ_fo) expr)
            | `Proposition (`App (k, [])) ->
              (sigma k :> ('a, typ_fo) expr)
            | _ -> expr
          with Nonlinear -> expr
        end
      | `ArithTerm t ->
        begin match ArithTerm.destruct srk t with
          | `App (k, []) -> (sigma k :> ('a, typ_fo) expr)
          | `Binop (`Mod, s, t) ->
            begin
              try
                (mk_mod srk (simplify s) (simplify t) :> ('a, typ_fo) expr)
              with Nonlinear -> expr
            end
          | _ -> expr
        end
      | `ArrTerm _ -> assert false)
    expr

(* Compute the GCD of all coefficients in an affine term (with integral
   coefficients) *)
let coefficient_gcd term =
  BatEnum.fold (fun gcd (qq, _) ->
      match QQ.to_zz qq with
      | None -> assert false
      | Some zz -> ZZ.gcd zz gcd)
    ZZ.zero
    (V.enum term)

let common_denominator term =
  BatEnum.fold (fun den (qq, _) ->
      ZZ.lcm den (QQ.denominator qq))
    ZZ.one
    (V.enum term)

let map_arith_atoms srk f phi =
  let rewriter expr =
    match Expr.refine srk expr with
    | `Formula phi ->
      begin match Formula.destruct srk phi with
        | `Atom (`Arith (op, s, t)) -> (f op s t :> ('a, typ_fo) expr)
        | _ -> expr
      end
    | `ArithTerm _ 
    | `ArrTerm _ -> expr
  in
  rewrite srk ~up:rewriter phi

(* floor(term/divisor) + offset *)
type int_virtual_term =
  { term : V.t;
    divisor : ZZ.t;
    offset : ZZ.t }
  [@@deriving ord]

exception Equal_int_term of int_virtual_term

let pp_int_virtual_term srk formatter vt =
  begin
    if ZZ.equal vt.divisor ZZ.one then
      pp_linterm srk formatter vt.term
    else
      Format.fprintf formatter "@[floor(@[%a@ / %a@])@]"
        (pp_linterm srk) vt.term
        ZZ.pp vt.divisor
  end;
  if not (ZZ.equal vt.offset ZZ.zero) then
    Format.fprintf formatter " + %a@]" ZZ.pp vt.offset
  else
    Format.fprintf formatter "@]"

type virtual_term =
  | MinusInfinity
  | PlusEpsilon of V.t
  | Term of V.t

let pp_virtual_term srk formatter =
  function
  | MinusInfinity -> Format.pp_print_string formatter "-oo"
  | PlusEpsilon t ->
    Format.fprintf formatter "%a + epsilon" (pp_linterm srk) t
  | Term t -> pp_linterm srk formatter t

(* Loos-Weispfenning virtual substitution *) 
let virtual_substitution srk x virtual_term phi =
  let pivot_term x term =
    V.pivot (dim_of_sym x) (linterm_of srk term)
  in
  let replace_atom op s zero =
    assert (ArithTerm.equal zero (mk_real srk QQ.zero));

    (* s == s' + ax, x not in fv(s') *)
    let (a, s') = pivot_term x s in
    if QQ.equal a QQ.zero then
      match op with
      | `Eq -> mk_eq srk s zero
      | `Lt -> mk_lt srk s zero
      | `Leq -> mk_leq srk s zero
    else
      let soa = V.scalar_mul (QQ.inverse (QQ.negate a)) s' (* -s'/a *) in
      let mk_sub s t = of_linterm srk (V.add s (V.negate t)) in
      match op, virtual_term with
      | (`Eq, Term t) ->
        (* -s'/a = x = t <==> -s'/a = t *)
        mk_eq srk (mk_sub soa t) zero
      | (`Leq, Term t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a <= x = t <==> -s'/a <= t *)
          mk_leq srk (mk_sub soa t) zero
        else
          (* t = x <= -s'/a <==> t <= -s'/a *)
          mk_leq srk (mk_sub t soa) zero
      | (`Lt, Term t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = t <==> -s'/a < t *)
          mk_lt srk (mk_sub soa t) zero
        else
          (* t = x < -s'/a <==> t < -s'/a *)
          mk_lt srk (mk_sub t soa) zero
      | `Eq, _ -> mk_false srk
      | (_, PlusEpsilon t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = t + eps <==> -s'/a <= t *)
          (* -s'/a <= x = t + eps <==> -s'/a <= t *)
          mk_leq srk (mk_sub soa t) zero
        else
          (* t + eps = x < -s'/a <==> t < -s'/a *)
          (* t + eps = x <= -s'/a <==> t < -s'/a *)
          mk_lt srk (mk_sub t soa) zero
      | (_, MinusInfinity) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = -oo <==> false *)
          mk_false srk
        else
          (* -oo = x < -s'/a <==> true *)
          mk_true srk
  in
  map_arith_atoms srk replace_atom phi

(* Model based projection, as in described in Anvesh Komuravelli, Arie
   Gurfinkel, Sagar Chaki: "SMT-based Model Checking for Recursive Programs".
   Given a structure m, a constant symbol x, and a set of
   linear terms T, find a virtual term vt such that
   - vt is -t/a (where ax + t in T) and m |= x = -t/a
   - vt is -t/a + epsilon (where ax + t in T) and m |= -t/a < x and
                          m |= 's/b < x ==> (-s/b <= s/a) for all bx + s in T
   - vt is -oo otherwise *)
let mbp_virtual_term srk interp x atoms =
  if typ_symbol srk x != `TyReal then
    invalid_arg "mbp: cannot eliminate non-real symbols";

  let x_val =
    try Interpretation.real interp x
    with Not_found ->
      invalid_arg "mbp_virtual_term: no interpretation for constant"
  in
  let merge lower lower' =
    match lower, lower' with
    | None, x | x, None -> x
    | Some (lower, lower_val), Some (lower', lower_val') ->
      if QQ.lt lower_val lower_val' then
        Some (lower', lower_val')
      else
        Some (lower, lower_val)
  in

  let get_vt atom =
    match Interpretation.destruct_atom srk atom with
    | `Literal (_, _) -> None
    | `ArrEq _ -> None
    | `ArithComparison (op, s, t) ->
      let t =
        try V.add (linterm_of srk s) (V.negate (linterm_of srk t))
        with Nonlinear -> assert false
      in
      let (a, t') = V.pivot (dim_of_sym x) t in

      (* Atom is ax + t' op 0 *)
      if QQ.equal QQ.zero a then
        None
      else
        let toa = V.scalar_mul (QQ.inverse (QQ.negate a)) t' in
        let toa_val = evaluate_linterm (Interpretation.real interp) toa in
        match op with
        | `Eq -> raise (Equal_term toa)
        | `Leq when QQ.equal toa_val x_val -> raise (Equal_term toa)
        | `Lt | `Leq ->
          if QQ.lt a QQ.zero then
            (* Lower bound *)
            Some (toa, toa_val)
          else
            (* Upper bound: discard *)
            None
  in
  let vt =
    try
      begin match List.fold_left merge None (List.map get_vt atoms) with
      | Some (lower, _) -> PlusEpsilon lower
      | None -> MinusInfinity
      end
    with Equal_term t -> Term t
  in
  logf ~level:`trace "Virtual term for %a: %a"
    (pp_symbol srk) x
    (pp_virtual_term srk) vt;
  vt

(* Given a prenex formula phi, compute a pair (qf_pre, psi) such that
   - qf_pre is a quantifier prefix [(Q0, a0);...;(Qn, an)] where each Qi is
     either `Exists or `Forall, and each ai is a Skolem constant
   - psi is negation- and quantifier-free formula, and contains no free
     variables
   - every atom of in psi is either a propositial variable or an arithmetic
     atom of the form t < 0, t <= 0, or t = 0 or array equality 
   - phi is equivalent to Q0 a0.Q1 a1. ... Qn. an. psi
*)
let normalize srk phi =
  let phi = Formula.prenex srk phi in
  let zero = mk_real srk QQ.zero in
  let rewriter env expr =
    match Expr.refine_coarse srk expr with
    | `Formula phi ->
      (begin match Formula.destruct srk phi with
         | `Proposition (`Var i) -> mk_const srk (Env.find env i)
         | `Atom (`Arith (`Eq, s, t)) -> mk_eq srk (mk_sub srk s t) zero
         | `Atom (`Arith (`Leq, s, t)) -> mk_leq srk (mk_sub srk s t) zero
         | `Atom (`Arith (`Lt, s, t)) -> mk_lt srk (mk_sub srk s t) zero
         | _ -> phi
       end :> ('a, typ_fo) expr)
    | `Term t ->
      begin match Term.destruct srk t with
        | `Var (i, _) ->
          begin
            try mk_const srk (Env.find env i)
            with Not_found -> invalid_arg "Quantifier.normalize: free variable"
          end
        | _ -> expr
      end
  in
  let rec go env phi =
    match Formula.destruct srk phi with
    | `Quantify (qt, name, typ, psi) ->
      let k = mk_symbol srk ~name (typ :> Syntax.typ) in
      let (qf_pre, psi) = go (Env.push k env) psi in
      ((qt,k)::qf_pre, psi)
    | _ -> ([], rewrite srk ~down:(nnf_rewriter srk) ~up:(rewriter env) phi)
  in
  go Env.empty phi

let simplify_atom srk op s t =
  let zero = mk_real srk QQ.zero in
  let destruct_int term =
    match ArithTerm.destruct srk term with
    | `Real q ->
      begin match QQ.to_zz q with
        | Some z -> z
        | None -> invalid_arg "simplify_atom: non-integral value"
      end
    | _ -> invalid_arg "simplify_atom: non-constant"
  in
  let (s, op) =
    let s =
      if ArithTerm.equal t zero then s
      else mk_sub srk s t
    in
    match op with
    | `Lt when (expr_typ srk s = `TyInt) ->
      (SrkSimplify.simplify_term srk (mk_add srk [s; mk_real srk QQ.one]), `Leq)
    | _ -> (SrkSimplify.simplify_term srk s, op)
  in
  (* Scale a linterm with rational coefficients so that all coefficients are
     integral *)
  let zz_linterm term =
    let qq_linterm = linterm_of srk term in
    let multiplier = 
      BatEnum.fold (fun multiplier (qq, _) ->
          ZZ.lcm (QQ.denominator qq) multiplier)
        ZZ.one
        (V.enum qq_linterm)
    in
    (multiplier, V.scalar_mul (QQ.of_zz multiplier) qq_linterm)
  in
  match op with
  | `Eq | `Leq ->
    begin match ArithTerm.destruct srk s with
    | `Binop (`Mod, dividend, modulus) ->
      (* Divisibility constraint *)
      let modulus = destruct_int modulus in
      let (multiplier, lt) = zz_linterm dividend in
      `Divides (ZZ.mul multiplier modulus, lt)
    | `Unop (`Neg, s') ->
      begin match ArithTerm.destruct srk s' with
        | `Binop (`Mod, dividend, modulus) ->
          if op = `Leq then
            (* trivial *)
            `CompareZero (`Leq, V.zero)
          else
            (* Divisibility constraint *)
            let modulus = destruct_int modulus in
            let (multiplier, lt) = zz_linterm dividend in
            `Divides (ZZ.mul multiplier modulus, lt)
        | _ -> `CompareZero (op, snd (zz_linterm s))
      end
    | `Add [x; y] ->
      begin match ArithTerm.destruct srk x, ArithTerm.destruct srk y with
        | `Real k, `Binop (`Mod, dividend, modulus)
        | `Binop (`Mod, dividend, modulus), `Real k when QQ.lt k QQ.zero && op = `Eq ->
          let (multiplier, lt) = zz_linterm dividend in
          let modulus = destruct_int modulus in
          if ZZ.equal multiplier ZZ.one && QQ.lt k (QQ.of_zz modulus) then
            let lt = V.add_term k const_dim lt in
            `Divides (modulus, lt)
          else
            `CompareZero (op, snd (zz_linterm s))
        | `Real k, `Unop (`Neg, z) | `Unop (`Neg, z), `Real k when QQ.equal k QQ.one ->
          begin match ArithTerm.destruct srk z with
            | `Binop (`Mod, dividend, modulus) ->
              let modulus = destruct_int modulus in
              let (multiplier, lt) = zz_linterm dividend in
              `NotDivides (ZZ.mul multiplier modulus, lt)
            | _ -> `CompareZero (op, snd (zz_linterm s))
          end
        | _, _ -> `CompareZero (op, snd (zz_linterm s))
      end
    | _ -> `CompareZero (op, snd (zz_linterm s))
    end
  | `Lt ->
    begin match ArithTerm.destruct srk s with
      | `Binop (`Mod, dividend, modulus) ->
        (* Indivisibility constraint: dividend % modulus < 0. *)
        let modulus = destruct_int modulus in
        let (multiplier, lt) = zz_linterm dividend in
        `NotDivides (ZZ.mul multiplier modulus, lt)

      | `Unop (`Neg, s') ->
        begin match ArithTerm.destruct srk s' with
          | `Binop (`Mod, dividend, modulus) ->
            (* Indivisibility constraint: dividend % modulus > 0 *)
            let modulus = destruct_int modulus in
            let (multiplier, lt) = zz_linterm dividend in
            `NotDivides (ZZ.mul multiplier modulus, lt)
          | _ -> `CompareZero (`Lt, snd (zz_linterm s))
        end

      | _ -> `CompareZero (`Lt, snd (zz_linterm s))
    end

let is_presburger_atom srk atom =
  try
    begin match Interpretation.destruct_atom srk atom with
      | `Literal (_, _) -> true
      | `ArrEq _ -> false
      | `ArithComparison (op, s, t) ->
        ignore (simplify_atom srk op s t);
        true
    end
  with _ -> false

let mk_divides srk divisor term =
  assert (ZZ.lt ZZ.zero divisor);
  if ZZ.equal divisor ZZ.one || V.is_zero term then
    mk_true srk
  else
    let gcd = ZZ.gcd (coefficient_gcd term) divisor in
    let divisor = QQ.of_zz (ZZ.div divisor gcd) in
    let term = V.scalar_mul (QQ.of_zzfrac ZZ.one gcd) term in
    mk_eq srk
      (mk_mod srk (of_linterm srk term) (mk_real srk divisor))
      (mk_real srk QQ.zero)

let _mk_not_divides srk divisor term =
  assert(ZZ.lt ZZ.zero divisor);
  if ZZ.equal divisor ZZ.one || V.is_zero term then
    mk_false srk
  else
    let gcd = ZZ.gcd (coefficient_gcd term) divisor in
    assert (ZZ.lt ZZ.zero gcd);
    let divisor = QQ.div (QQ.of_zz divisor) (QQ.of_zz gcd) in
    let term = V.scalar_mul (QQ.of_zzfrac ZZ.one gcd) term in

    mk_lt srk
      (mk_neg srk (mk_mod srk (of_linterm srk term) (mk_real srk divisor)))
      (mk_real srk QQ.zero)

let term_of_virtual_term srk vt =
  let term = of_linterm srk vt.term in
  let offset = mk_real srk (QQ.of_zz vt.offset) in
  let term_over_div =
    if ZZ.equal vt.divisor ZZ.one then
      term
    else
      mk_floor srk (mk_div srk term (mk_real srk (QQ.of_zz vt.divisor)))
  in
  mk_add srk [term_over_div; offset]

let miniscope srk phi : 'a formula =
  let flip qtyp =
    match qtyp with
    | `Exists -> `Forall
    | `Forall -> `Exists
  in
  let pass_thru qtyp expr_typ =
    match qtyp, expr_typ with
    | `Exists, `Exists -> `Pass
    | `Exists, `Forall -> `Blocking
    | `Forall, `Forall -> `Pass
    | `Forall, `Exists -> `Blocking
    | `Forall, `And -> `Pass
    | `Exists, `And -> `Blocking
    | `Exists, `Or -> `Pass
    | `Forall, `Or -> `Blocking
  in
  let mk_quant qtyp name typ phi =
    match qtyp with
    | `Exists -> mk_exists srk ~name typ phi
    | `Forall -> mk_forall srk ~name typ phi
  in
  let mk_junct jtyp juncts =
    match jtyp with
    | `Or -> mk_or srk juncts
    | `And -> mk_and srk juncts
  in
  (* This is the logic for pushing the quantifier qnt into formula node.*)
  let rec pushdown qtyp name typ phi =
    let dec_fv_by_1 phi =
      substitute
        srk
        (fun (ind, typ) -> mk_var srk (ind - 1) typ)
        phi
    in
    let reorder_first_2_qnts phi =
      substitute
        srk
        (fun (ind, typ) ->
           if ind = 0 then mk_var srk 1 typ
           else if ind = 1 then mk_var srk 0 typ
           else mk_var srk ind typ)
        phi
    in
    let handle_juncts jtyp juncts =
      let l1, l2 =
        List.partition (fun conj ->
            BatHashtbl.mem (free_vars conj) 0)
          juncts
      in
      let l2' = List.map dec_fv_by_1 l2 in
      let c =
        if pass_thru qtyp jtyp = `Pass || List.length l1 <= 1 then (
          mk_junct jtyp (List.map (pushdown qtyp name typ) l1))
        else (mk_quant qtyp name typ (mk_junct jtyp l1))
      in
      mk_junct jtyp (c :: l2')
    in
    if not (BatHashtbl.mem (free_vars phi) 0)
    then dec_fv_by_1 phi
    else (
      match Formula.destruct srk phi with
      | `Tru -> assert false
      | `Fls -> assert false
      (* TODO: distribute over ITE, or elim ITE. *)
      | `Atom _  | `Proposition _ | `Ite _ -> mk_quant qtyp name typ phi
      | `Not phi -> mk_not srk (pushdown (flip qtyp) name typ phi)
      | `And juncts -> handle_juncts `And juncts
      | `Or juncts -> handle_juncts `Or juncts
      | `Quantify((q, n, t, p)) ->
        if pass_thru qtyp q = `Blocking then
          mk_quant qtyp name typ phi
        else (
          mk_quant
            q
            n
            t
            (pushdown qtyp name typ (reorder_first_2_qnts p))))
  in
  let alg = function
   | `Quantify (qtyp, name, typ, phi) ->
      pushdown qtyp name typ phi
   | open_phi -> Formula.construct srk open_phi
  in
  let phi = (Formula.eval srk alg phi) in
  phi

exception Redundant_path
module Skeleton = struct
  type exists_move =
    | MInt of int_virtual_term
    | MReal of V.t
    | MBool of bool
          [@@deriving ord]

  let pp_move srk formatter move =
    match move with
    | MInt vt -> pp_int_virtual_term srk formatter vt
    | MReal t -> pp_linterm srk formatter t
    | MBool true -> Format.pp_print_string formatter "true"
    | MBool false -> Format.pp_print_string formatter "false"

  let substitute srk x move phi =
    match move with
    | MInt vt ->
      let replacement = term_of_virtual_term srk vt in
      substitute_const
        srk
        (fun p -> if p = x then replacement else mk_const srk p)
        phi
    | MReal t ->
      let replacement = of_linterm srk t in
      substitute_const
        srk
        (fun p -> if p = x then replacement else mk_const srk p)
        phi
    | MBool vb ->
      let replacement = match vb with
        | true -> mk_true srk
        | false -> mk_false srk
      in
      substitute_const srk
        (fun p -> if p = x then replacement else mk_const srk p)
        phi

  let evaluate_move model move =
    match move with
    | MInt vt ->
      begin match QQ.to_zz (evaluate_linterm model vt.term) with
        | None -> assert false
        | Some tv ->
          ZZ.add (Mpzf.fdiv_q tv vt.divisor) vt.offset
          |> QQ.of_zz
      end
    | MReal t -> evaluate_linterm model t
    | MBool _ -> invalid_arg "evaluate_move"

  let substitute_implicant interp x move implicant =
    let srk = Interpretation.get_context interp in
    let is_true phi =
      match Formula.destruct srk phi with
      | `Tru -> true
      | _ -> false
    in
    match move with
    | MInt vt ->
      (* floor(term/div) + offset ~> (term - ([[term]] mod div))/div + offset,
         and add constraint that div | (term - ([[term]] mod div)) *)
      let term_val =
        let term_qq = evaluate_linterm (Interpretation.real interp) vt.term in
        match QQ.to_zz term_qq with
        | None -> assert false
        | Some zz -> zz
      in
      let remainder =
        Mpzf.fdiv_r term_val vt.divisor
      in
      let numerator =
        V.add_term (QQ.of_zz (ZZ.negate remainder)) const_dim vt.term
      in
      let replacement =
        V.scalar_mul (QQ.inverse (QQ.of_zz vt.divisor)) numerator
        |> V.add_term (QQ.of_zz vt.offset) const_dim
        |> of_linterm srk
      in

      assert (QQ.equal
                (Interpretation.evaluate_term interp replacement)
                (evaluate_move (Interpretation.real interp) move));
      let subst =
        substitute_const srk
          (fun p -> if p = x then replacement else mk_const srk p)
      in
      let divides = mk_divides srk vt.divisor numerator in
      BatList.filter (not % is_true) (divides::(List.map subst implicant))
    | _ ->
      BatList.filter_map (fun atom ->
          let atom' = substitute srk x move atom in
          if is_true atom' then None else Some atom')
        implicant

  let const_of_move move =
    match move with
    | MReal t -> const_of_linterm t
    | MInt vt ->
      if ZZ.equal vt.divisor ZZ.one then const_of_linterm vt.term
      else None
    | MBool _ -> invalid_arg "const_of_move"

  module MM = BatMap.Make(struct type t = exists_move [@@deriving ord] end)
  module CoarseGrain = struct
    type t =
      | SForall of symbol * symbol * t
      | SExists of symbol * (t MM.t)
      | SEmpty

    let pp srk formatter skeleton =
      let open Format in
      let rec pp formatter = function
        | SForall (_, sk, t) ->
          fprintf formatter "@[<v 2>(forall %a:@;%a)@]" (pp_symbol srk) sk pp t
        | SExists (k, mm) ->
          let pp_elt formatter (move, skeleton) =
            fprintf formatter "%a:@;@[%a@]@\n"
              (pp_move srk) move
              pp skeleton
          in
          let pp_sep formatter () = Format.fprintf formatter "@;" in
          fprintf formatter "@[<v 2>(exists %a:@;@[<v 0>%a@])@]"
            (pp_symbol srk) k
            (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt) (MM.enum mm)
        | SEmpty -> ()
      in
      pp formatter skeleton

    let rec size = function
      | SEmpty -> 0
      | SForall (_, _, t) -> 1 + (size t)
      | SExists (_, mm) ->
        MM.enum mm
        /@ (fun (_, t) -> size t)
        |> BatEnum.sum
        |> (+) 1

    let rec nb_paths = function
      | SEmpty -> 1
      | SForall (_, _, t) -> nb_paths t
      | SExists (_, mm) ->
        MM.enum mm
        /@ (fun (_, t) -> nb_paths t)
        |> BatEnum.sum

    let empty = SEmpty

    (* Create a new skeleton where the only path is the given path *)
    let mk_path srk path =
      let rec go = function
        | [] -> SEmpty
        | (`Forall k)::path ->
          let sk = mk_symbol srk ~name:(show_symbol srk k) (typ_symbol srk k) in
          SForall (k, sk, go path)
        | (`Exists (k, move))::path ->
          SExists (k, MM.add move (go path) MM.empty)
      in
      go path

    (* Add a path (corresponding to a new instantiation of the existential
       variables of some formula) to a skeleton.  Raise Redundant_path if this
       path already belonged to the skeleton. *)
    let add_path srk path skeleton =
      let rec go path skeleton =
        match path, skeleton with
        | ([], SEmpty) ->
          (* path was already in skeleton *)
          raise Redundant_path

        | (`Forall k::path, SForall (k', sk, skeleton)) ->
          assert (k = k');
          SForall (k, sk, go path skeleton)

        | (`Exists (k, move)::path, SExists (k', mm)) ->
          assert (k = k');
          let subskeleton =
            try go path (MM.find move mm)
            with Not_found -> mk_path srk path
          in
          SExists (k, MM.add move subskeleton mm)
        | `Exists (_, _)::_, SForall (_, _, _) | (`Forall _)::_, SExists (_, _) ->
          assert false
        | ([], _) ->
          assert false
        | (_, SEmpty) ->
          assert false
      in
      match skeleton with
      | SEmpty -> mk_path srk path
      | _ -> go path skeleton

    (* Used for incremental construction of the winning formula:
         (winning_formula skeleton phi)
                                   = \/_p winning_path_formula p skeleton phi *)
    let path_winning_formula srk path skeleton phi =
      let rec go path skeleton =
        match path, skeleton with
        | ([], SEmpty) -> phi
        | (`Forall k::path, SForall (k', sk, skeleton)) ->
          assert (k = k');
          let sk_const = mk_const srk sk in
          substitute_const srk
            (fun sym -> if k = sym then sk_const else mk_const srk sym)
            (go path skeleton)
        | (`Exists (k, move)::path, SExists (k', mm)) ->
          assert (k = k');
          substitute srk k move (go path (MM.find move mm))
        | (_, _) -> assert false
      in
      go path skeleton

    (* winning_formula skeleton phi is valid iff skeleton is a winning skeleton
       for the formula phi *)
    let winning_formula srk skeleton phi =
      let rec go = function
        | SEmpty -> phi
        | SForall (k, sk, skeleton) ->
          let sk_const = mk_const srk sk in
          substitute_const srk
            (fun sym -> if k = sym then sk_const else mk_const srk sym)
            (go skeleton)

        | SExists (k, mm) ->
          MM.enum mm
          /@ (fun (move, skeleton) -> substitute srk k move (go skeleton))
          |> BatList.of_enum
          |> mk_or srk
      in
      go skeleton

    let rec paths = function
      | SEmpty -> [[]]
      | SForall (k, _, skeleton) ->
        List.map (fun path -> (`Forall k)::path) (paths skeleton)
      | SExists (k, mm) ->
        BatEnum.fold (fun rest (move, skeleton) ->
            (List.map (fun path -> (`Exists (k, move))::path) (paths skeleton))
            @rest)
          []
          (MM.enum mm)
  end

  module FineGrain = struct
    module IM = SrkUtil.Int.Map

(*    (* A path is actually a tree since we need a path for every conjuct, not just one conjuct *)
    type path =
      | PForall of symbol * path
      | PExists of symbol * exists_move * path
      | POr of int * path
      | PAnd of path list
      | PEmpty *)

    (* A skeleton is a representation of a set of paths *)
    type t =
      | SForall of symbol * symbol * t
      | SExists of symbol * (t MM.t)
      | SOr of t IM.t   (* For a list of disjuncts [a0, ..., an] we have a partial function from [0,n] to a sub-skeleton for the given disjunct *)
      | SAnd of (symbol * t) list  (* For a list of conjucts [a0, ..., an] we have [(b0, s0), ..., (bn, sn)]. Each (bi, si) is a skeleton for ai and a boolean used to iteratively encode the winning formula of the skeleton when si is updated *)
      | SEmpty

    let pp srk formatter skeleton =
      let open Format in
      let pp_sep formatter () = fprintf formatter "@;" in
      let rec pp formatter = function
        | SForall (_, sk, t) ->
          fprintf formatter "@[<v 2>(forall %a@;%a)@]" (pp_symbol srk) sk pp t
        | SExists (k, mm) ->
          let pp_elt formatter (move, skeleton) =
            fprintf formatter "%a => @;@[%a@]@\n"
              (pp_move srk) move
              pp skeleton
          in
          fprintf formatter "@[<v 2>(exists %a;@;@[<v 0>%a@])@]"
            (pp_symbol srk) k
            (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt) (MM.enum mm)
        | SOr im ->
          let pp_elt formatter (i, skeleton) =
            fprintf formatter "in%d;@;@[%a@]@\n" i pp skeleton
          in
          fprintf formatter "@[<v 2>(or ;@;@[<v 0>%a@])@]" (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt) (IM.enum im)
        | SAnd sub_skels ->
          let pp_elt formatter (_, skeleton) =
            fprintf formatter "%a" pp skeleton
          in
          fprintf formatter "@[<v 2>(and ;@;@[<v 0>%a@])@]" (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt) (BatList.enum sub_skels)
        | SEmpty -> fprintf formatter "@[Atom @]"
      in
      pp formatter skeleton

    let rec size = function
      | SEmpty -> 0
      | SAnd sub_skels -> List.fold_left (fun sz (_, t) -> sz + (size t)) 1 sub_skels
      | SOr im -> IM.enum im /@ (fun (_, t) -> size t) |> BatEnum.sum |> (+) 1
      | SForall (_, _, t) -> 1 + (size t)
      | SExists (_, mm) -> MM.enum mm /@ (fun (_, t) -> size t) |> BatEnum.sum |> (+) 1

    (* we count number of simple paths *)
    let rec nb_paths = function
      | SEmpty -> 1
      | SAnd sub_skels -> BatList.enum sub_skels /@ (fun (_, t) -> nb_paths t) |> BatEnum.sum
      | SOr im -> IM.enum im /@ (fun (_, t) -> nb_paths t) |> BatEnum.sum
      | SForall (_, _, t) -> nb_paths t
      | SExists (_, mm) -> MM.enum mm /@ (fun (_, t) -> nb_paths t) |> BatEnum.sum

(*    (* Create a new skeleton where the only path is the given path *)
    let mk_path srk path =
      let rec go = function
        | PEmpty -> SEmpty
        | PAnd sub_paths -> SAnd (List.map (fun p -> (mk_symbol srk ~name:"B" `TyBool, go p)) sub_paths)
        | POr (i, p) -> SOr (IM.singleton i (go p))
        | PForall (k, p) ->
          let sk = mk_symbol srk ~name:(show_symbol srk k) (typ_symbol srk k) in
          SForall (k, sk, (go p))
        | PExists (k, m, p) -> SExists (k, (MM.singleton m (go p)))
      in
      go path *)

(*    let add_path srk path skeleton =
      let rec go path skeleton =
        match path, skeleton with
        | (PEmpty, SEmpty) ->
          (* path was already in skeleton *)
          raise Redundant_path
        | (PAnd sub_paths), (SAnd sub_skels) ->
          let (redundant, sub_skels) =
            List.fold_left2 (fun (r, sub_skels) p (b, t) ->
              try (false, (b, go p t) :: sub_skels)
              with Redundant_path -> (r, (b, t) :: sub_skels)
            ) (true, []) sub_paths sub_skels
          in
          if redundant then raise Redundant_path;
          SAnd (List.rev sub_skels)
        | (POr (i, p)), (SOr im) ->
          let sub_skel =
            try go p (IM.find i im)
            with Not_found -> mk_path srk p
          in
          SOr (IM.add i sub_skel im)
        | (PForall (k', p)), (SForall (k, sk, t)) ->
          assert (k = k');
          SForall (k, sk, go p t)
        | (PExists (k', m, p)), (SExists (k, mm)) ->
          assert (k = k');
          let sub_skel =
            try go p (MM.find m mm)
            with Not_found -> mk_path srk p
          in
          SExists (k, MM.add m sub_skel mm)
        | _, _ -> assert false
      in
      match skeleton with
      | SEmpty -> mk_path srk path
      | _ -> go path skeleton *)

    (* union two skeletons together *)
    let union _ skel1 skel2 =
      let rec go s1 s2 =
        match s1, s2 with
        | SEmpty, SEmpty -> SEmpty
        | SAnd sub_skels1, SAnd sub_skels2 ->
          SAnd (List.map2 (fun (b, t1) (_, t2) -> (b, go t1 t2)) sub_skels1 sub_skels2)
        | SOr im1, SOr im2 ->
          SOr (IM.merge (fun _ t1 t2 ->
                           match t1, t2 with
                           | Some t1, Some t2 -> Some (go t1 t2)
                           | Some _, _ -> t1
                           | _, _ -> t2) im1 im2)
        | SForall (k, sk, skel1), SForall (k', _, skel2) ->
          assert (k = k');
          SForall (k, sk, go skel1 skel2)
        | SExists (k, mm1), SExists (k', mm2) ->
          assert (k = k');
          SExists (k, MM.merge (fun _ t1 t2 ->
                                  match t1, t2 with
                                  | Some t1, Some t2 -> Some (go t1 t2)
                                  | Some _, _ -> t1
                                  | _, _ -> t2) mm1 mm2)
        | _, _ -> assert false
      in
      match skel1, skel2 with
      | SEmpty, _ -> skel2
      | _, SEmpty -> skel1
      | _, _ -> go skel1 skel2


    let losing_formula' srk skeleton phi =
      let rec go phi skeleton =
        match phi, skeleton with
        | `Atom phi, SEmpty -> [phi], []
        | `And sub_phis, SAnd sub_skels ->
          let (psis, conds) =
            List.fold_left2 (fun (psis, conds) phi (b, skel) ->
              let b = mk_const srk b in
              let (psis', conds') = go phi skel in
              (b :: psis, List.rev_append (List.map (fun psi -> mk_if srk psi b) psis')
                                          (List.rev_append conds' conds))
            ) ([], []) sub_phis sub_skels
          in
          ([mk_and srk psis], conds)
        | `Or sub_phis, SOr im ->
          IM.fold (fun i skel (psis, conds) ->
            let phi = List.nth sub_phis i in
            let (psis', conds') = go phi skel in
            (List.rev_append psis' psis, List.rev_append conds' conds)
          ) im ([], [])
        | `Forall (k, phi), SForall (k', sk, t) ->
          assert (k = k');
          let subst = substitute_const srk (fun sym -> if sym = k then mk_const srk sk else mk_const srk sym) in
          let (psis, conds) = go phi t in
          (List.map subst psis, List.map subst conds)
        | `Exists (k, phi), SExists (k', mm) ->
          assert (k = k');
          MM.fold (fun move skel (psis, conds) ->
            let (psis', conds') = go phi skel in
            let subst = substitute srk k move in
            (List.rev_append (List.map subst psis') psis, List.rev_append (List.map subst conds') conds)
          ) mm ([], [])
        | _, _ -> assert false
      in
      match phi, skeleton with
      | `Atom _, SEmpty -> go phi skeleton
      | _, SEmpty -> ([mk_false srk], [])
      | _, _ -> go phi skeleton

    (* Used for incremental construction of the losing formula (negation of winning formula):
       Note: winning_formula skeleton phi = /\_p winning_path_formula p skeleton phi

       Thus, we can conclude:
       (winning_formula (skeleton U new_skeleton) phi)
                             = (winning_formula skeleton phi)
                               \/ (winning_formula (new_skeleton \ skeleton) phi)

       Our encoding of conjunts (b, skel)
       b with the condition skel => b, ensures that we can consider simple paths, rather
       than complete paths (which reduces the # of paths from exponential to linear).
       Note: This encoding preserves equi-satisfiability of !(winning_formula skeleton phi)

       if (union_losing_formula srk skel new_skel phi) = phis then
         [(losing_formula srk skel phi) /\ (/\_{phi \in phis} phi)]
                                  <==>
                  (losing_formula srk (skel U new_skel))
                          Equisatisfiable with
                 !(winning_formula srk (skel U new_skel))
     *)
    let union_losing_formula srk skeleton new_skeleton phi =
      let rec go phi skel new_skel =
        match phi, skel, new_skel with
        | `Atom _, SEmpty, SEmpty -> [], [] (* redundant *)
        | `And sub_phis, SAnd sub_skels, SAnd new_sub_skels ->
          let rec fold3 conds phis skels new_skels =
            match phis, skels, new_skels with
            | [], [], [] -> conds
            | phi :: phis, (b, t) :: skels, (_, t') :: new_skels ->
              let (psis, psi_conds) = go phi t t' in
              let b = mk_const srk b in
              fold3 (List.rev_append
                      (List.map (fun psi -> mk_if srk psi b) psis)
                      (List.rev_append psi_conds conds)) phis skels new_skels
            | _, _, _ -> assert false
          in
          [], fold3 [] sub_phis sub_skels new_sub_skels
        | `Or sub_phis, SOr im, SOr new_im ->
          IM.fold (fun i new_sub_skel (psis, conds) ->
            let phi = List.nth sub_phis i in
            let (psis', conds') =
              match IM.find_opt i im with
              | Some sub_skel -> go phi sub_skel new_sub_skel
              | None -> losing_formula' srk new_sub_skel phi
            in
            (List.rev_append psis' psis, List.rev_append conds' conds)
          ) new_im ([], [])
        | `Forall (k, phi), SForall (k', sk, t), SForall (k'', _, new_t) ->
          assert (k == k' && k' == k'');
          let psis, conds = go phi t new_t in
          let subst = substitute_const srk (fun sym -> if k = sym then mk_const srk sk else mk_const srk sym) in
          (List.map subst psis, List.map subst conds)
        | `Exists (k, phi), SExists (k', mm), SExists (k'', new_mm) ->
          assert (k == k' && k' == k'');
          MM.fold (fun move new_sub_skel (psis, conds) ->
            let (psis', conds') =
              match MM.find_opt move mm with
              | Some sub_skel -> go phi sub_skel new_sub_skel
              | None -> losing_formula' srk new_sub_skel phi
            in
            let subst = substitute srk k move in
            (List.rev_append (List.map subst psis') psis, List.rev_append (List.map subst conds') conds)
          ) new_mm ([], [])
        | _, _, _ -> assert false
      in
      let (phis, conds) =
        match skeleton, new_skeleton with
        | _, SEmpty -> [], []
        | SEmpty, _ -> losing_formula' srk new_skeleton phi
        | _, _ -> go phi skeleton new_skeleton
      in
      List.rev_append (List.map (mk_not srk) phis) conds

    let losing_formula srk skeleton phi =
      let (psis, conds) = losing_formula' srk skeleton phi in
      mk_and srk (List.rev_append (List.map (mk_not srk) psis) conds)

(*
    (* winning_formula skeleton phi is valid iff skeleton is a winning skeleton for phi
       The winning formula of the union of two skeletons for phi is the disjunction of each's winning formula for phi *)
    let winning_formula srk skeleton phi =
      let rec go phi skeleton =
        match phi, skeleton with
        | (`Atom phi), SEmpty -> phi
        | (`And sub_phis), (SAnd sub_skels) ->
          mk_and srk (List.map2 (fun phi (_, skel) -> go phi skel) sub_phis sub_skels)
        | (`Or sub_phis), (SOr im) ->
          IM.enum im
          /@ (fun (i, t) -> go (List.nth sub_phis i) t)
          |> BatList.of_enum
          |> mk_or srk
        | (`Forall (k', psi)), (SForall (k, sk, t)) ->
          assert (k' = k);
          let sk_const = mk_const srk sk in
          substitute_const srk (fun sym -> if k = sym then sk_const else mk_const srk sym) (go psi t)
        | (`Exists (k', psi)), (SExists (k, mm)) ->
          assert (k' = k);
          MM.enum mm
          /@ (fun (m, t) -> substitute srk k m (go psi t))
          |> BatList.of_enum
          |> mk_or srk
        | _, _ -> assert false
      in go phi skeleton

    let rec paths = function
      | SEmpty -> [ PEmpty ]
      | SAnd sub_skels ->
        (List.map (fun (_, skel) -> paths skel) sub_skels
        |> List.map (fun sub_paths -> BatList.enum sub_paths)
        |> SrkUtil.tuples)
        /@ (fun sub_paths -> PAnd sub_paths)
        |> BatList.of_enum
      | SOr im ->
        BatEnum.fold (fun rest (i, t) ->
            (List.map (fun p -> POr (i, p)) (paths t)) @rest)
          []
          (IM.enum im)
      | SForall (k, _, t) ->
        List.map (fun p -> PForall (k, p)) (paths t)
      | SExists (k, mm) ->
        BatEnum.fold (fun rest (m, t) ->
            (List.map (fun p -> PExists (k, m, p)) (paths t)) @rest)
          []
          (MM.enum mm) *)
  end
end

let select_real_term srk interp x atoms =
  let merge (lower1, upper1) (lower2, upper2) =
    let lower =
      match lower1, lower2 with
      | (x, None) | (None, x) -> x
      | (Some (s, s_val, s_strict), Some (t, t_val, t_strict)) ->
        if QQ.lt t_val s_val
        then
          Some (s, s_val, s_strict)
        else
          let strict =
            (QQ.equal t_val s_val && (s_strict || t_strict))
            || t_strict
          in
          Some (t, t_val, strict)
    in
    let upper =
      match upper1, upper2 with
      | (x, None) | (None, x) -> x
      | (Some (s, s_val, s_strict), Some (t, t_val, t_strict)) ->
        if QQ.lt s_val t_val
        then
          Some (s, s_val, s_strict)
        else
          let strict =
            (QQ.equal t_val s_val && (s_strict || t_strict))
            || t_strict
          in
          Some (t, t_val, strict)
    in
    (lower, upper)
  in
  let x_val = Interpretation.real interp x in
  let bound_of_atom atom =
    match Interpretation.destruct_atom srk atom with
    | `Literal (_, _) 
    | `ArrEq _ -> (None, None)
    | `ArithComparison (op, s, t) ->
      let t = V.add (linterm_of srk s) (V.negate (linterm_of srk t)) in

      let (a, t') = V.pivot (dim_of_sym x) t in

      (* Atom is ax + t' op 0 *)
      if QQ.equal QQ.zero a then
        (None, None)
      else
        let toa = V.scalar_mul (QQ.inverse (QQ.negate a)) t' in
        let toa_val = evaluate_linterm (Interpretation.real interp) toa in
        if op = `Eq || (QQ.equal toa_val x_val && op = `Leq) then
          raise (Equal_term toa)
        else if QQ.lt a QQ.zero then
          (* Lower bound *)
          (Some (toa, toa_val, op = `Lt), None)
        else
          (* Upper bound *)
          (None, Some (toa, toa_val, op = `Lt))
  in
  let bound_of_atom atom =
    if Symbol.Set.mem x (symbols atom) then
      bound_of_atom atom
    else
      (None, None)
  in
  try
    match List.fold_left merge (None, None) (List.map bound_of_atom atoms) with
    | (Some (t, _, false), _) | (_, Some (t, _, false)) ->
      (logf ~level:`trace "Found equal(?) term: %a = %a"
         (pp_symbol srk) x
         (pp_linterm srk) t;
       t)
    | (Some (s, _, _), None) ->
      logf ~level:`trace "Found lower bound: %a < %a"
        (pp_linterm srk) s
        (pp_symbol srk) x;
      V.add s (const_linterm (QQ.of_int (1)))
    | (None, Some (t, _, _)) ->
      logf ~level:`trace "Found upper bound: %a < %a"
        (pp_symbol srk) x
        (pp_linterm srk) t;
      V.add t (const_linterm (QQ.of_int (-1)))
    | (Some (s, _, _), Some (t, _, _)) ->
      logf ~level:`trace "Found interval: %a < %a < %a"
        (pp_linterm srk) s
        (pp_symbol srk) x
        (pp_linterm srk) t;
      V.scalar_mul (QQ.of_frac 1 2) (V.add s t)
    | (None, None) -> V.zero (* Value of x is irrelevant *)
  with Equal_term t ->
    (logf ~level:`trace "Found equal term: %a = %a"
       (pp_symbol srk) x
       (pp_linterm srk) t;
     t)

let select_int_term srk interp x atoms =
  assert (typ_symbol srk x == `TyInt);
  let merge bound bound' =
    match bound, bound' with
    | (`Lower (s, s_val), `Lower (t, t_val)) ->
        if ZZ.lt t_val s_val then
          `Lower (s, s_val)
        else
          `Lower (t, t_val)
    | (`Upper (s, s_val), `Upper (t, t_val)) ->
        if ZZ.lt s_val t_val then
          `Upper (s, s_val)
        else
          `Upper (t, t_val)
    | (`Lower (t, t_val), _) | (_, `Lower (t, t_val)) -> `Lower (t, t_val)
    | (`Upper (t, t_val), _) | (_, `Upper (t, t_val)) -> `Upper (t, t_val)
    | `None, `None -> `None
  in
  let eval = evaluate_linterm (Interpretation.real interp) in
  let x_val = match QQ.to_zz (Interpretation.real interp x) with
    | Some zz -> zz
    | None -> assert false
  in
  (* delta = gcd { lcm(d,a) : d | ax + t or not(d | ax + t) in atoms }.  If
     [[vt]](m) = [[x]](m) mod delta, then for every divisilibity atom
       d | ax + t
     which appears in phi, we have
       m |= (d | ax + t)   <==>   m |= (d | a(vt) + t *)
  let delta =
    List.fold_left
      (fun delta atom ->
         match Interpretation.destruct_atom srk atom with
         | `Literal (_, _) -> delta
         | `ArrEq _ -> delta
         | `ArithComparison (op, s, t) ->
           match simplify_atom srk op s t with
           | `Divides (divisor, t) | `NotDivides (divisor, t) ->
             let a = match QQ.to_zz (V.coeff (dim_of_sym x) t) with
               | None -> assert false
               | Some zz -> ZZ.abs zz
             in
             if ZZ.equal ZZ.zero a then delta
             else ZZ.lcm (ZZ.div divisor (ZZ.gcd divisor a)) delta
           | _ -> delta)
      ZZ.one
      atoms
  in
  assert (ZZ.lt ZZ.zero delta);
  let evaluate_vt vt =
    let real_val =
      Skeleton.evaluate_move (Interpretation.real interp) (Skeleton.MInt vt)
    in
    match QQ.to_zz real_val with
    | Some v -> v
    | None -> assert false
  in
  let bound_of_atom atom =
    match Interpretation.destruct_atom srk atom with
    | `Literal (_, _) -> `None
    | `ArrEq _ -> `None
    | `ArithComparison (op, s, t) ->
      match simplify_atom srk op s t with
      | `CompareZero (op, t) ->
        begin
          let (a, t) = V.pivot (dim_of_sym x) t in
          let a = match QQ.to_zz a with
            | None -> assert false
            | Some zz -> zz
          in
          if ZZ.equal a ZZ.zero then
            `None
          else if ZZ.compare a ZZ.zero > 0 then
            (* ax + t (<|<=) 0 --> upper bound of floor(-t/a) *)
            (* x (<|<=) floor(-t/a) + ([[x - floor(-t/a)]] mod delta) - delta *)
            let numerator =
              if op = `Lt then
                (* a*floor(((numerator-1) / a) < numerator *)
                V.add_term (QQ.of_int (-1)) const_dim (V.negate t)
              else
                V.negate t
            in

            let rhs_val = (* [[floor(numerator / a)]] *)
              match QQ.to_zz (eval numerator) with
              | Some num -> Mpzf.fdiv_q num a
              | None -> assert false
            in
            let vt =
              { term = numerator;
                divisor = a;
                offset = Mpzf.cdiv_r (ZZ.sub x_val rhs_val) delta }
            in
            let vt_val = evaluate_vt vt in

            assert (ZZ.equal (ZZ.modulo (ZZ.sub vt_val x_val) delta) ZZ.zero);
            assert (ZZ.leq x_val vt_val);
            begin
              let axv = ZZ.mul a vt_val in
              let tv = match QQ.to_zz (eval t) with
                | Some zz -> ZZ.negate zz
                | None -> assert false
              in
              match op with
              | `Lt -> assert (ZZ.lt axv tv)
              | `Leq -> assert (ZZ.leq axv tv)
              | `Eq -> assert (ZZ.equal axv tv)
            end;
            begin match op with
              | `Eq -> raise (Equal_int_term vt)
              | _ ->
                `Upper (vt, evaluate_vt vt)
            end
          else
            let a = ZZ.negate a in

            (* (-a)x + t <= 0 --> lower bound of ceil(t/a) = floor((t+a-1)/a) *)
            (* (-a)x + t < 0 --> lower bound of ceil(t+1/a) = floor((t+a)/a) *)
            let numerator =
              if op = `Lt then
                V.add_term (QQ.of_zz a) const_dim t
              else
                V.add_term (QQ.of_zz (ZZ.sub a ZZ.one)) const_dim t
            in
            let rhs_val = (* [[floor(numerator / a)]] *)
              match QQ.to_zz (eval numerator) with
              | Some num -> Mpzf.fdiv_q num a
              | None -> assert false
            in

            let vt =
              { term = numerator;
                divisor = a;
                offset = Mpzf.fdiv_r (ZZ.sub x_val rhs_val) delta }
            in
            let vt_val = evaluate_vt vt in
            assert (ZZ.equal (ZZ.modulo (ZZ.sub vt_val x_val) delta) ZZ.zero);
            assert (ZZ.leq vt_val x_val);
            begin
              let axv = ZZ.mul a vt_val in
              let tv = match QQ.to_zz (eval t) with
                | Some zz -> zz
                | None -> assert false
              in
              match op with
              | `Lt -> assert (ZZ.lt tv axv)
              | `Leq -> assert (ZZ.leq tv axv)
              | `Eq -> assert (ZZ.equal tv axv)
            end;
            begin match op with
              | `Eq -> raise (Equal_int_term vt)
              | _ ->
                `Lower (vt, evaluate_vt vt)
            end
        end
      | _ ->
        `None
  in
  let bound_of_atom atom =
    if Symbol.Set.mem x (symbols atom) then
      bound_of_atom atom
    else
      `None
  in
  let vt_val vt =
    let tval = match QQ.to_zz (eval vt.term) with
      | Some zz -> zz
      | None -> assert false
    in
    ZZ.add (Mpzf.fdiv_q tval vt.divisor) vt.offset
  in
  match List.fold_left merge `None (List.map bound_of_atom atoms) with
  | `Lower (vt, _) ->
    logf ~level:`trace "Found lower bound: %a < %a"
      (pp_int_virtual_term srk) vt
      (pp_symbol srk) x;
    assert (ZZ.equal (Mpzf.fdiv_r x_val delta) (Mpzf.fdiv_r (vt_val vt) delta));
    vt
  | `Upper (vt, _) ->
    logf ~level:`trace "Found upper bound: %a < %a"
      (pp_symbol srk) x
      (pp_int_virtual_term srk) vt;
    assert (ZZ.equal (Mpzf.fdiv_r x_val delta) (Mpzf.fdiv_r (vt_val vt) delta));
    vt
  | `None ->
    (* Value of x is irrelevant *)
    logf ~level:`trace "Irrelevant: %a" (pp_symbol srk) x;
    let value = Linear.const_linterm (QQ.of_zz (ZZ.modulo x_val delta)) in
    { term = value; divisor = ZZ.one; offset = ZZ.zero }

let select_int_term srk interp x atoms =
  try
    select_int_term srk interp x atoms
  with
  | Equal_int_term vt -> vt
  | Nonlinear ->
    Log.errorf "(nonlinear) select_int_term atoms:";
    List.iter (fun atom ->
        if not (is_presburger_atom srk atom) then
          Log.errorf ">%a" (Formula.pp srk) atom)
      atoms;
    assert false
  | Invalid_argument msg ->
    Log.errorf  "(inv arg) select_int_term atoms: %s" msg;
    List.iter (fun atom -> Log.errorf ">%a" (Formula.pp srk) atom) atoms;
    assert false


(* Given an interpretation M and a cube C with M |= C, find a cube C'
   such that M |= C' |= C, and C' does not contain any floor terms. *)
let specialize_floor_cube srk model cube =
  let div_constraints = ref [] in
  let add_div_constraint divisor term =
    let div =
      mk_eq srk (mk_mod srk term (mk_real srk (QQ.of_zz divisor))) (mk_real srk QQ.zero)
    in
    div_constraints := div::(!div_constraints)
  in
  let replace_floor expr = match destruct srk expr with
    | `Unop (`Floor, t) ->
       let v = linterm_of srk t in
       let divisor = common_denominator v in
       let qq_divisor = QQ.of_zz divisor in
       let dividend = of_linterm srk (V.scalar_mul qq_divisor v) in
       let remainder =
         QQ.modulo (Interpretation.evaluate_term model dividend) qq_divisor
       in
       let dividend' = mk_sub srk dividend (mk_real srk remainder) in
       let replacement =
         V.add_term
           (QQ.negate (QQ.div remainder qq_divisor))
           Linear.const_dim
           v
         |> of_linterm srk
       in
       assert (QQ.equal
                 (Interpretation.evaluate_term model replacement)
                 (QQ.of_zz (QQ.floor (Interpretation.evaluate_term model t))));

       add_div_constraint divisor dividend';
       (replacement :> ('a,typ_fo) expr)
    | `Binop (`Mod, t, m) ->
       begin match destruct srk m with
       | `Real m ->
          let replacement =
            mk_real srk (QQ.modulo (Interpretation.evaluate_term model t) m)
          in
          let m = match QQ.to_zz m with
            | Some m -> m
            | None -> assert false
          in
          add_div_constraint m (mk_sub srk t replacement);
          (replacement :> ('a,typ_fo) expr)
       | _ -> expr
       end
    | _ -> expr
  in
  let cube' = List.map (rewrite srk ~up:replace_floor) cube in
  (!div_constraints)@cube'


let select_implicant srk interp ?(env=Env.empty) phi =
  match Interpretation.select_implicant interp ~env phi with
  | Some atoms ->
    logf ~level:`trace "Implicant Atoms:";
    List.iter
      (fun atom -> logf ~level:`trace ">%a" (Formula.pp srk) atom)
      atoms;
    Some (specialize_floor_cube srk interp atoms)
  | None -> None

(** The type of modules implementing Strategy Improvement *)
module type StrategyImprovement = sig
  (** Satisfiability via strategy improvement *)
  val simsat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

  (** Satisfiability via strategy improvement, forwards version *)
  val simsat_forward : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

  (** Alternating quantifier optimization *)
  val maximize : 'a context -> 'a formula -> 'a arith_term -> [ `Bounded of QQ.t
                                                              | `Infinity
                                                              | `MinusInfinity
                                                              | `Unknown ]
  (** Alternating quantifier satisfiability *)
  val easy_sat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

  type 'a skeleton
  type 'a move
  type 'a strategy
  type 'a normalized_formula

  val pp_skeleton : 'a context -> Format.formatter -> 'a skeleton -> unit
  val show_skeleton : 'a context -> 'a skeleton -> string

  val winning_skeleton : 'a context -> 'a normalized_formula ->
    [ `Sat of 'a skeleton
    | `Unsat of 'a skeleton
    | `Unknown ]

  val pp_strategy : 'a context -> Format.formatter -> 'a strategy -> unit
  val show_strategy : 'a context -> 'a strategy -> string

  (** Compute a winning SAT/UNSAT strategy for a normalized formula *)
  val winning_strategy : 'a context -> 'a normalized_formula ->
      [ `Sat of 'a strategy
      | `Unsat of 'a strategy
      | `Unknown ]

  (** Check that a SAT strategy is in fact a winning Strategy. (To verify
      an UNSAT stragey provide the negation of the normalized function) *)
  val check_strategy : 'a context -> 'a normalized_formula -> 'a strategy -> bool

  (** take a formula and return a normalized formula *)
  val normalize : 'a context -> 'a formula -> 'a normalized_formula

  val pp_normal : 'a context -> Format.formatter -> 'a normalized_formula -> unit
end

type 'a cg_formula = ([`Forall | `Exists] * symbol) list * 'a formula
module CoarseGrainStrategyImprovement = struct
  module CSS = struct
    type 'a ctx =
      { formula : 'a formula;
        not_formula : 'a formula; (* Negated formula *)
        mutable skeleton : Skeleton.CoarseGrain.t; (* skeleton for formula *)

        solver : 'a Smt.Solver.t;
        srk : 'a context;
      }

    let reset ctx =
      Smt.Solver.reset ctx.solver;
      ctx.skeleton <- Skeleton.CoarseGrain.SEmpty

    let add_path ctx path =
      let srk = ctx.srk in
      try
        ctx.skeleton <- Skeleton.CoarseGrain.add_path srk path ctx.skeleton;
        let win =
          Skeleton.CoarseGrain.path_winning_formula srk path ctx.skeleton ctx.formula
        in
        Smt.Solver.add ctx.solver [mk_not srk win]
      with Redundant_path -> ()

    (* Check if a given skeleton is winning.  If not, synthesize a
       counter-strategy. *)
    let get_counter_strategy select_term ?(parameters=None) ctx =
      logf ~level:`trace "%a" (Skeleton.CoarseGrain.pp ctx.srk) ctx.skeleton;
      let parameters =
        match parameters with
        | Some p -> p
        | None   -> Interpretation.empty ctx.srk
      in
      match Smt.Solver.get_model ctx.solver with
      | `Unsat ->
        logf "Winning formula is valid";
        `Unsat
      | `Unknown -> `Unknown
      | `Sat m ->
        logf "Winning formula is not valid";

        (* Using the model m, synthesize a counter-strategy which beats the
           strategy skeleton.  This is done by traversing the skeleton: on the
           way down, we build a model of the *negation* of the formula using the
           labels on the path to the root.  On the way up, we find elimination
           terms for each universally-quantified variable using model-based
           projection.  *)
        let rec counter_strategy path_model skeleton =
          let open Skeleton in
          let open CoarseGrain in
          logf ~level:`trace "Path model: %a" Interpretation.pp path_model;
          match skeleton with
          | SForall (k, sk, skeleton) ->
            let path_model =
              Interpretation.add
                k
                (Interpretation.value m sk)
                path_model
           in
            logf ~level:`trace "Forall %a (%a)"
              (pp_symbol ctx.srk) k
              (pp_symbol ctx.srk) sk;
            let (counter_phi, counter_paths) =
              counter_strategy path_model skeleton
            in
            let move = select_term path_model k counter_phi in
            logf ~level:`trace "Found move: %a = %a"
              (pp_symbol ctx.srk) k
              (Skeleton.pp_move ctx.srk) move;
            let counter_phi =
              Skeleton.substitute_implicant path_model k move counter_phi
            in
            let counter_paths =
              List.map (fun path -> (`Exists (k, move))::path) counter_paths
            in
            (counter_phi, counter_paths)
          | SExists (k, mm) ->
            let (counter_phis, paths) =
              MM.enum mm
              /@ (fun (move, skeleton) ->
                  let path_model =
                    match move with
                    | Skeleton.MBool bool_val ->
                      Interpretation.add_bool k bool_val path_model
                    | _ ->
                      let mv =
                        Skeleton.evaluate_move
                          (Interpretation.real path_model)
                          move
                      in
                      Interpretation.add_real k mv path_model
                  in
                  let (counter_phi, counter_paths) =
                    counter_strategy path_model skeleton
                  in
                  let counter_phi =
                    Skeleton.substitute_implicant path_model k move counter_phi
                  in
                  let counter_paths =
                    List.map (fun path -> (`Forall k)::path) counter_paths
                  in
                  (counter_phi, counter_paths))
              |> BatEnum.uncombine
            in
            (BatList.concat (BatList.of_enum counter_phis),
             BatList.concat (BatList.of_enum paths))
          | SEmpty ->
            logf ~level:`trace "Path model: %a" Interpretation.pp path_model;
            logf ~level:`trace "not_phi: %a" (Formula.pp ctx.srk) ctx.not_formula;
            let phi_implicant =
              match select_implicant ctx.srk path_model ctx.not_formula with
              | Some x -> x
              | None -> assert false
            in
            (phi_implicant, [[]])
        in
        `Sat (snd (counter_strategy parameters ctx.skeleton))

    (* Check to see if the matrix of a prenex formula is satisfiable.  If it is,
       initialize a sat/unsat strategy skeleton pair. *)
    let initialize_pair select_term srk qf_pre phi =
      match Smt.get_model srk phi with
      | `Unsat -> `Unsat
      | `Unknown -> `Unknown
      | `Sat phi_model ->
        logf "Found initial model";
        (* Create paths for sat_skeleton & unsat_skeleton *)
        let f (qt, x) (sat_path, unsat_path, atoms) =
          let move = select_term phi_model x atoms in
          let (sat_path, unsat_path) = match qt with
            | `Exists ->
              ((`Exists (x, move))::sat_path,
               (`Forall x)::unsat_path)
            | `Forall ->
              ((`Forall x)::sat_path,
               (`Exists (x, move))::unsat_path)
          in
          (sat_path,
           unsat_path,
           Skeleton.substitute_implicant phi_model x move atoms)
        in
        let (sat_path, unsat_path, _) =
          match select_implicant srk phi_model phi with
          | Some implicant -> List.fold_right f qf_pre ([], [], implicant)
          | None -> assert false
        in
        let not_phi = snd (normalize srk (mk_not srk phi)) in
        let sat_ctx =
          let skeleton = Skeleton.CoarseGrain.mk_path srk sat_path in
          let win =
            Skeleton.CoarseGrain.path_winning_formula srk sat_path skeleton phi
          in
          let solver = Smt.mk_solver srk in
          Smt.Solver.add solver [mk_not srk win];
          { formula = phi;
            not_formula = not_phi;
            skeleton = skeleton;
            solver = solver;
            srk = srk }
        in
        let unsat_ctx =
          let skeleton = Skeleton.CoarseGrain.mk_path srk unsat_path in
          let win =
            Skeleton.CoarseGrain.path_winning_formula srk unsat_path skeleton not_phi
          in
          let solver = Smt.mk_solver srk in
          Smt.Solver.add solver [mk_not srk win];
          { formula = not_phi;
            not_formula = phi;
            skeleton = skeleton;
            solver = solver;
            srk = srk }
        in
        logf "Initial SAT strategy:@\n%a"
          (Skeleton.CoarseGrain.pp srk) sat_ctx.skeleton;
        logf "Initial UNSAT strategy:@\n%a"
          (Skeleton.CoarseGrain.pp srk) unsat_ctx.skeleton;
        `Sat (sat_ctx, unsat_ctx)

    let is_sat select_term sat_ctx unsat_ctx =
      let round = ref 0 in
      let old_paths = ref (-1) in
      let rec is_sat () =
        incr round;
        logf ~level:`trace ~attributes:[`Blue;`Bold]
          "Round %d: Sat [%d/%d], Unsat [%d/%d]"
          (!round)
          (Skeleton.CoarseGrain.size sat_ctx.skeleton)
          (Skeleton.CoarseGrain.nb_paths sat_ctx.skeleton)
          (Skeleton.CoarseGrain.size unsat_ctx.skeleton)
                (Skeleton.CoarseGrain.nb_paths unsat_ctx.skeleton);
        let paths = Skeleton.CoarseGrain.nb_paths sat_ctx.skeleton in
        assert (paths > !old_paths);
        old_paths := paths;
        logf ~attributes:[`Blue;`Bold] "Checking if SAT wins (%d)"
          (Skeleton.CoarseGrain.nb_paths sat_ctx.skeleton);
        match get_counter_strategy select_term sat_ctx with
        | `Sat paths -> (List.iter (add_path unsat_ctx) paths; is_unsat ())
        | `Unsat -> `Sat
        | `Unknown -> `Unknown
      and is_unsat () =
        logf ~attributes:[`Blue;`Bold] "Checking if UNSAT wins (%d)"
          (Skeleton.CoarseGrain.nb_paths unsat_ctx.skeleton);
        match get_counter_strategy select_term unsat_ctx with
        | `Sat paths -> (List.iter (add_path sat_ctx) paths; is_sat ())
        | `Unsat -> `Unsat
        | `Unknown -> `Unknown
      in
      is_sat ()

    let max_improve_rounds = ref 10

    (* Try to find a "good" initial model of phi by solving a non-accumulating
       version of the satisfiability game.  This game can go into an infinite
       loop (paper beats rock beats scissors beats paper...), so we detect
       cycles by saving every strategy we've found and quitting when we get a
       repeat or when we hit max_improve_rounds. *)
    let initialize_pair select_term srk qf_pre phi =
      let unsat_skeleton = ref Skeleton.CoarseGrain.empty in
      match initialize_pair select_term srk qf_pre phi with
      | `Unsat -> `Unsat
      | `Unknown -> `Unknown
      | `Sat (sat_ctx, unsat_ctx) ->
        let round = ref 0 in
        let rec is_sat () =
          incr round;
          logf "Improve round: %d" (!round);
          logf ~attributes:[`Blue;`Bold] "Checking if SAT wins (%d)"
            (Skeleton.CoarseGrain.size sat_ctx.skeleton);
          if (!round) = (!max_improve_rounds) then
            `Sat (sat_ctx, unsat_ctx)
          else
            match get_counter_strategy select_term sat_ctx with
            | `Sat [path] ->
              begin
                try
                  unsat_skeleton := Skeleton.CoarseGrain.add_path srk path (!unsat_skeleton);
                  reset unsat_ctx;
                  add_path unsat_ctx path;
                  is_unsat ()
                with Redundant_path -> `Sat (sat_ctx, unsat_ctx)
              end
            | `Sat _ -> assert false
            | `Unsat -> `Sat (sat_ctx, unsat_ctx)
            | `Unknown -> `Unknown
        and is_unsat () =
          logf ~attributes:[`Blue;`Bold] "Checking if UNSAT wins (%d)"
            (Skeleton.CoarseGrain.size unsat_ctx.skeleton);
          match get_counter_strategy select_term unsat_ctx with
          | `Sat paths -> (reset sat_ctx;
                           List.iter (add_path sat_ctx) paths;
                           is_sat ())
          | `Unsat -> `Unsat
          | `Unknown -> `Unknown
        in
        is_sat ()

    let _minimize_skeleton param_interp ctx =
      let solver = Smt.mk_solver ctx.srk in
      let paths = Skeleton.CoarseGrain.paths ctx.skeleton in
      let path_guards =
        List.map (fun _ -> mk_const ctx.srk (mk_symbol ctx.srk `TyBool)) paths
      in
      let psis =
        let winning_formula path =
          Skeleton.CoarseGrain.path_winning_formula ctx.srk path ctx.skeleton ctx.formula
          |> Interpretation.substitute param_interp
        in
        List.map2 (fun path guard ->
            mk_or ctx.srk [mk_not ctx.srk guard;
                           mk_not ctx.srk (winning_formula path)])
          paths
          path_guards
      in
      let path_of_guard guard =
        List.fold_left2 (fun res g path ->
            if Formula.equal g guard then Some path
            else res)
          None
          path_guards
          paths
        |> (function
            | Some x -> x
            | None -> assert false)
      in
      Smt.Solver.add solver psis;
      match Smt.Solver.get_unsat_core solver path_guards with
      | `Sat -> assert false
      | `Unknown -> assert false
      | `Unsat core ->
        List.fold_left
          (fun skeleton core_guard ->
             try Skeleton.CoarseGrain.add_path ctx.srk (path_of_guard core_guard) skeleton
             with Redundant_path -> skeleton)
          Skeleton.CoarseGrain.empty
          core
  end

  let simsat_forward_core srk qf_pre phi =
    let select_term model x atoms =
      match typ_symbol srk x with
      | `TyInt -> Skeleton.MInt (select_int_term srk model x atoms)
      | `TyReal -> Skeleton.MReal (select_real_term srk model x atoms)
      | `TyBool -> Skeleton.MBool (Interpretation.bool model x)
      | `TyFun (_, _) -> assert false
      | `TyArr -> assert false
    in

    (* If the quantifier prefix leads with an existential, check satisfiability
       of the negated sentence instead, then negate the result.  We may now
       assume that the outer-most quantifier is universal. *)
    let (qf_pre, phi, negate) =
      match qf_pre with
      | (`Exists, _)::_ ->
        let phi = snd (normalize srk (mk_not srk phi)) in
        let qf_pre =
          List.map (function
              | (`Exists, x) -> (`Forall, x)
              | (`Forall, x) -> (`Exists, x))
            qf_pre
        in
        (qf_pre, phi, true)
      | _ ->
        (qf_pre, phi, false)
    in
    match CSS.initialize_pair select_term srk qf_pre phi with
    | `Unsat ->
      (* Matrix is unsat -> any unsat strategy is winning *)
      let path =
        qf_pre |> List.map (function
            | `Forall, k ->
              begin match typ_symbol srk k with
                | `TyReal ->
                  `Exists (k, Skeleton.MReal (Linear.const_linterm QQ.zero))
                | `TyInt ->
                  let vt =
                    { term = Linear.const_linterm QQ.zero;
                      divisor = ZZ.one;
                      offset = ZZ.zero }
                  in
                  `Exists (k, Skeleton.MInt vt)
                | `TyBool -> `Exists (k, Skeleton.MBool true)
                | _ -> assert false
              end
            | `Exists, k -> `Forall k)
      in
      let skeleton = Skeleton.CoarseGrain.add_path srk path Skeleton.CoarseGrain.empty in
      if negate then `Sat skeleton
      else `Unsat skeleton

    | `Unknown -> `Unknown
    | `Sat (sat_ctx, _) ->
      let not_phi = sat_ctx.CSS.not_formula in
      let assert_param_constraints ctx parameter_interp =
        let open CSS in
        BatEnum.iter (function
            | (k, `Real qv) ->
              Smt.Solver.add ctx.solver
                [mk_eq srk (mk_const srk k) (mk_real srk qv)]
            | (k, `Bool false) ->
              Smt.Solver.add ctx.solver [mk_not srk (mk_const srk k)]
            | (k, `Bool true) ->
              Smt.Solver.add ctx.solver [mk_const srk k]
            | (_, `Fun _) -> ())
          (Interpretation.enum parameter_interp)
      in
      let mk_sat_ctx skeleton parameter_interp =
        let open CSS in
        let win =
          Skeleton.CoarseGrain.winning_formula srk skeleton phi
          |> Interpretation.substitute parameter_interp
        in
        let ctx =
          { formula = phi;
            not_formula = not_phi;
            skeleton = skeleton;
            solver = Smt.mk_solver srk;
            srk = srk }
        in
        Smt.Solver.add ctx.solver [mk_not srk win];
        assert_param_constraints ctx parameter_interp;
        ctx
      in
      let mk_unsat_ctx skeleton parameter_interp =
        let open CSS in
        let win =
          Skeleton.CoarseGrain.winning_formula srk skeleton not_phi
          |> Interpretation.substitute parameter_interp
        in
        let ctx =
          { formula = not_phi;
            not_formula = phi;
            skeleton = skeleton;
            solver = Smt.mk_solver srk;
            srk = srk }
        in
        Smt.Solver.add ctx.solver [mk_not srk win];
        assert_param_constraints ctx parameter_interp;
        ctx
      in

      (* Peel leading existential quantifiers off of a skeleton.  Fails if there
         is more than one move for an existential in the prefix.  *)
      let rec existential_prefix = function
        | Skeleton.CoarseGrain.SExists (k, mm) ->
          begin match BatList.of_enum (Skeleton.MM.enum mm) with
            | [(move, skeleton)] ->
              let (ex_pre, sub_skeleton) = existential_prefix skeleton in
              ((k, move)::ex_pre, sub_skeleton)
            | _ -> assert false
          end
        | skeleton -> ([], skeleton)
      in
      let rec universal_prefix = function
        | Skeleton.CoarseGrain.SForall (k, _, skeleton) -> k::(universal_prefix skeleton)
        | _ -> []
      in
      let skeleton_of_paths paths =
        List.fold_left
          (fun skeleton path ->
             try Skeleton.CoarseGrain.add_path srk path skeleton
             with Redundant_path -> skeleton)
          Skeleton.CoarseGrain.empty
          paths
      in

      (* Compute a winning strategy for the remainder of the game, after the
         prefix play determined by parameter_interp.  skeleton is an initial
         candidate strategy for one of the players, which begins with
         universals. *)
      let rec solve_game polarity param_interp ctx =
        logf ~attributes:[`Green] "Solving game %s (%d/%d)"
          (if polarity then "SAT" else "UNSAT")
          (Skeleton.CoarseGrain.nb_paths ctx.CSS.skeleton)
          (Skeleton.CoarseGrain.size ctx.CSS.skeleton);
        logf ~level:`trace "Parameters: %a" Interpretation.pp param_interp;
        let res =
          try
            CSS.get_counter_strategy
              select_term
              ~parameters:(Some param_interp)
              ctx
          with Not_found -> assert false
        in
        match res with
        | `Unknown -> `Unknown
        | `Unsat ->
          (* No counter-strategy to the strategy of the active player => active
             player wins *)
          `Sat ctx.CSS.skeleton
        | `Sat paths ->
          let unsat_skeleton = skeleton_of_paths paths in
          let (ex_pre, sub_skeleton) = existential_prefix unsat_skeleton in
          let param_interp' =
            List.fold_left (fun interp (k, move) ->
                match move with
                | Skeleton.MBool bv -> Interpretation.add_bool k bv interp
                | move ->
                  Interpretation.add_real
                    k
                    (Skeleton.evaluate_move (Interpretation.real interp) move)
                    interp)
              param_interp
              ex_pre
          in
          let sub_ctx =
            if polarity then
              mk_unsat_ctx sub_skeleton param_interp'
            else
              mk_sat_ctx sub_skeleton param_interp'
          in
          match solve_game (not polarity) param_interp' sub_ctx with
          | `Unknown -> `Unknown
          | `Sat skeleton ->
            (* Inactive player wins *)
            let skeleton =
              List.fold_right
                (fun (k, move) skeleton ->
                   let mm = Skeleton.MM.add move skeleton Skeleton.MM.empty in
                   Skeleton.CoarseGrain.SExists (k, mm))
                ex_pre
                skeleton
            in
            `Unsat skeleton
          | `Unsat skeleton' ->
            (* There is a counter-strategy for the strategy of the inactive
               player => augment strategy for the active player & try again *)
            let open CSS in
            let forall_prefix =
              List.map (fun x -> `Forall x) (universal_prefix ctx.skeleton)
            in
            let add_path path =
              try
                let path = forall_prefix@path in
                ctx.skeleton <- Skeleton.CoarseGrain.add_path srk path ctx.skeleton;
                let win =
                  Skeleton.CoarseGrain.path_winning_formula srk path ctx.skeleton ctx.formula
                  |> Interpretation.substitute param_interp
                in
                Smt.Solver.add ctx.solver [mk_not srk win]
              with Redundant_path -> ()
            in
            List.iter add_path (Skeleton.CoarseGrain.paths skeleton');
            solve_game polarity param_interp ctx
      in
      match solve_game true (Interpretation.empty srk) sat_ctx with
      | `Unknown -> `Unknown
      | `Sat skeleton -> if negate then `Unsat skeleton else `Sat skeleton
      | `Unsat skeleton -> if negate then `Sat skeleton else `Unsat skeleton

  let simsat_core srk qf_pre phi =
    let select_term model x phi =
      match typ_symbol srk x with
      | `TyInt -> Skeleton.MInt (select_int_term srk model x phi)
      | `TyReal -> Skeleton.MReal (select_real_term srk model x phi)
      | `TyBool -> Skeleton.MBool (Interpretation.bool model x)
      | `TyFun (_, _) -> assert false
      | `TyArr -> assert false
    in
    match CSS.initialize_pair select_term srk qf_pre phi with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat (sat_ctx, unsat_ctx) ->
      CSS.reset unsat_ctx;
      CSS.is_sat select_term sat_ctx unsat_ctx

  let simsat srk phi =
    let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
    let (qf_pre, phi) = normalize srk phi in
    let qf_pre =
      (List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre
    in
    CSS.max_improve_rounds := 2;
    logf "Quantifier prefix: %s"
      (String.concat "" (List.map (function (`Forall, _) -> "A" | (`Exists, _) -> "E") qf_pre));
    simsat_core srk qf_pre phi

  let simsat_forward srk phi =
    let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
    let (qf_pre, phi) = normalize srk phi in
    let qf_pre =
      (List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre
    in
    match simsat_forward_core srk qf_pre phi with
    | `Sat _ -> `Sat
    | `Unsat _ -> `Unsat
    | `Unknown -> `Unknown

  let maximize_feasible srk phi t =
    let objective_constants = fold_constants Symbol.Set.add t Symbol.Set.empty in
    let constants = fold_constants Symbol.Set.add phi objective_constants in
    let (qf_pre, phi) = normalize srk phi in
    let qf_pre =
      ((List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre)
    in

    (* First, check if the objective function is unbounded.  This is done by
       checking satisfiability of the formula:
         forall i. exists ks. phi /\ t >= i
    *)
    let objective = mk_symbol srk ~name:"objective" `TyReal in
    let qf_pre_unbounded = (`Forall, objective)::qf_pre in
    let phi_unbounded =
      mk_and srk [
        phi;
        mk_leq srk (mk_sub srk (mk_const srk objective) t) (mk_real srk QQ.zero)
      ]
    in
    let not_phi_unbounded =
      snd (normalize srk (mk_not srk phi_unbounded))
    in
    (* Always select [[objective]](m) as the value of objective *)
    let select_term m x phi =
      if x = objective then
        Skeleton.MReal (const_linterm (Interpretation.real m x))
      else
        match typ_symbol srk x with
        | `TyInt -> Skeleton.MInt (select_int_term srk m x phi)
        | `TyReal -> Skeleton.MReal (select_real_term srk m x phi)
        | `TyBool -> Skeleton.MBool (Interpretation.bool m x)
        | `TyFun (_, _) -> assert false
        | `TyArr -> assert false
    in
    CSS.max_improve_rounds := 1;
    let init =
      CSS.initialize_pair select_term srk qf_pre_unbounded phi_unbounded
    in
    match init with
    | `Unsat -> `MinusInfinity
    | `Unknown -> `Unknown
    | `Sat (sat_ctx, unsat_ctx) ->
      (* Skolem constant associated with the (universally quantified) objective
         bound *)
      let objective_skolem =
        match sat_ctx.CSS.skeleton with
        | Skeleton.CoarseGrain.SForall (_, sk, _) -> sk
        | _ -> assert false
      in
      let rec check_bound bound =
        begin
          match bound with
          | None -> ()
          | Some b ->
            CSS.reset unsat_ctx;
            Smt.Solver.add sat_ctx.CSS.solver [
              mk_lt srk (mk_const srk objective_skolem) (mk_real srk b)
            ]
        end;
        match CSS.is_sat select_term sat_ctx unsat_ctx with
        | `Unknown -> `Unknown
        | `Sat ->
          begin match bound with
            | Some b -> `Bounded b
            | None -> `Infinity
          end
        | `Unsat ->

          (* Find the largest constant which has been selected as an (UNSAT)
             move for the objective bound, and the associated sub-skeleton *)
          let (opt, opt_skeleton) = match unsat_ctx.CSS.skeleton with
            | Skeleton.CoarseGrain.SExists (_, mm) ->
              BatEnum.filter (fun (move, skeleton) ->
                  let move_val = match Skeleton.const_of_move move with
                    | Some qq -> qq
                    | None -> assert false
                  in
                  let win =
                    let win_not_unbounded =
                      Skeleton.CoarseGrain.winning_formula srk skeleton not_phi_unbounded
                    in
                    mk_and
                      srk
                      [mk_not srk win_not_unbounded;
                       mk_eq srk (mk_real srk move_val) (mk_const srk objective)]
                  in
                  Smt.is_sat srk win = `Unsat)
                (Skeleton.MM.enum mm)
              /@ (fun (v, skeleton) -> match Skeleton.const_of_move v with
                  | Some qq -> (qq, skeleton)
                  | None -> assert false)
              |> BatEnum.reduce (fun (a, a_skeleton) (b, b_skeleton) ->
                  if QQ.lt a b then (b, b_skeleton)
                  else (a, a_skeleton))
            | _ -> assert false
          in

          logf "Objective function is bounded by %a" QQ.pp opt;

          (* Get the negation of the winning formula for SAT corresponding to
             the sub-skeleton rooted below all of the constant symbols which
             appear in the objective.  This formula is weaker than phi, and the
             constant symbols in the objective are not bound. *)
          let bounded_phi =
            let open Skeleton in
            let open CoarseGrain in
            let rec go skeleton =
              match skeleton with
              | SEmpty -> SEmpty
              | SForall (k, _, subskeleton) ->
                if Symbol.Set.mem k objective_constants then go subskeleton
                else skeleton
              | SExists (_, _) -> skeleton
            in
            (Skeleton.CoarseGrain.winning_formula srk (go opt_skeleton) not_phi_unbounded)
            |> mk_not srk
          in
          logf "Bounded phi:@\n%a" (Formula.pp srk) bounded_phi;
          begin match SrkZ3.optimize_box srk bounded_phi [t] with
            | `Unknown ->
              Log.errorf "Failed to optimize - returning conservative bound";
              begin match bound with
                | Some b -> `Bounded b
                | None -> `Infinity
              end
            | `Sat [ivl] ->
              begin match bound, Interval.upper ivl with
                | Some b, Some x ->
                  logf "Bound %a --> %a" QQ.pp b QQ.pp x;
                  assert (QQ.lt x b)
                | _, None -> assert false
                | None, _ -> ()
              end;
              check_bound (Interval.upper ivl)
            | `Unsat | `Sat _ -> assert false
          end
      in
      check_bound None

  let maximize srk phi t =
    match simsat srk phi with
    | `Sat -> maximize_feasible srk phi t
    | `Unsat -> `MinusInfinity
    | `Unknown -> `Unknown

  let easy_sat srk phi =
    let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
    let (qf_pre, phi) = normalize srk phi in
    let qf_pre =
      (List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre
    in
    let select_term model x phi =
      match typ_symbol srk x with
      | `TyInt -> Skeleton.MInt (select_int_term srk model x phi)
      | `TyReal -> Skeleton.MReal (select_real_term srk model x phi)
      | `TyBool -> Skeleton.MBool (Interpretation.bool model x)
      | `TyFun (_, _) -> assert false
      | `TyArr -> assert false
    in
    match CSS.initialize_pair select_term srk qf_pre phi with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat (sat_ctx, _) ->
      match CSS.get_counter_strategy select_term sat_ctx with
      | `Unsat -> `Sat
      | `Unknown -> `Unknown
      | `Sat _ -> `Unknown

  type 'a skeleton = unit
  type 'a move = [ `Forall of symbol | `Exists of symbol * ('a, typ_fo) expr]
  type 'a strategy = Strategy of ('a formula * Skeleton.exists_move * 'a strategy) list
  type 'a normalized_formula = ([`Forall | `Exists] * symbol) list * 'a formula


  let pp_skeleton _ _ _ = ()
  let show_skeleton _ _ = failwith "CoarseGrain.show_skeleton unimplemented"

  let winning_skeleton _ _ = failwith "CoarseGrain.winning_skeleton unimplemented"

  let pp_strategy srk formatter (Strategy xs) =
    let open Format in
    let pp_sep formatter () = Format.fprintf formatter "@;" in
    let rec pp formatter = function
      | (Strategy []) -> ()
      | (Strategy xs) ->
        fprintf formatter "@;  @[<v 0>%a@]"
          (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt)
          (BatList.enum xs)
    and pp_elt formatter (guard, move, sub_strategy) =
      fprintf formatter "%a --> %a%a"
        (Formula.pp srk) guard
        (Skeleton.pp_move srk) move
        pp sub_strategy
    in
    fprintf formatter "@[<v 0>%a@]"
      (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt)
      (BatList.enum xs)

  let show_strategy srk = SrkUtil.mk_show (pp_strategy srk)

  (* Extract a winning strategy from a skeleton *)
  let extract_strategy _ _ _ =
    failwith "Quantifier.CoarseGrain.extract_strategy not implemented"

  let winning_strategy srk (qf_pre, phi) =
    match simsat_forward_core srk qf_pre phi with
    | `Sat skeleton ->
      logf "Formula is SAT.  Extracting strategy.";
      `Sat (extract_strategy srk skeleton phi)
    | `Unsat skeleton ->
      logf "Formula is UNSAT.  Extracting strategy.";
      `Unsat (extract_strategy srk skeleton (mk_not srk phi))
    | `Unknown -> `Unknown

  let check_strategy srk (qf_pre, phi) strategy =
    (* go qf_pre strategy computes a formula whose models correspond to playing
       phi according to the strategy *)
    let rec go qf_pre (Strategy xs) =
      match qf_pre with
      | [] ->
        assert (xs = []);
        mk_true srk
      | (`Exists, k)::qf_pre ->
        let has_move =
          xs |> List.map (fun (guard, move, sub_strategy) ->
              let move_formula =
                let open Skeleton in
                match move with
                | MInt vt ->
                  mk_eq srk (mk_const srk k) (term_of_virtual_term srk vt)
                | MReal linterm ->
                  mk_eq srk (mk_const srk k) (of_linterm srk linterm)
                | MBool true -> mk_const srk k
                | MBool false -> mk_not srk (mk_const srk k)
              in
              mk_and srk [guard; move_formula; go qf_pre sub_strategy])
          |> mk_or srk
        in
        let no_move =
          xs |> List.map (fun (guard, _, _) -> mk_not srk guard) |> mk_and srk
        in
        mk_or srk [has_move; no_move]
      | (`Forall, _)::qf_pre -> go qf_pre (Strategy xs)
    in
    let strategy_formula = go qf_pre strategy in
    Smt.is_sat srk (mk_and srk [strategy_formula; mk_not srk phi]) = `Unsat

  let normalize = normalize

  let pp_normal srk formatter (qf_pre, matrix) =
    let pp_quant formatter (qf, sym) =
      let qf =
        match qf with
        | `Exists -> "exists"
        | `Forall -> "forall"
      in
      Format.fprintf formatter "%s %a." qf (pp_symbol srk) sym
    in
    let pp_sep formatter _ = Format.fprintf formatter " " in
    Format.fprintf formatter "%a %a"
      (SrkUtil.pp_print_enum_nobox ~pp_sep:pp_sep pp_quant) (BatList.enum qf_pre)
      (Formula.pp srk) matrix

end

type 'a fg_formula = [ `Forall of symbol * 'a fg_formula
                     | `Exists of symbol * 'a fg_formula
                     | `And of 'a fg_formula list
                     | `Or of 'a fg_formula list
                     | `Atom of 'a formula ]

type 'a fg_skeleton = [ `Forall of symbol * 'a fg_skeleton
                      | `Exists of symbol * (('a, typ_fo) expr * 'a fg_skeleton) list
                      | `Or of (int * 'a fg_skeleton) list (* a partial function mapping of disjunts to skeletons *)
                      | `And of 'a fg_skeleton list (* a skeleton for each conjunct *)
                      | `Empty ]

module FineGrainStrategyImprovement = struct
  type 'a normalized_formula = 'a fg_formula

  let negate srk phi =
    let rec go = function
      | `Forall (k, phi) -> `Exists (k, (go phi))
      | `Exists (k, phi) -> `Forall (k, (go phi))
      | `And phis -> `Or (List.map go phis)
      | `Or phis -> `And (List.map go phis)
      | `Atom phi -> `Atom (snd (normalize srk (mk_not srk phi)))
    in go phi

  let normalize srk phi =
    let rec go env phi =
      let zero = mk_real srk QQ.zero in
      let go_term t =
        let rewriter expr =
          match Expr.refine srk expr with
          | `ArrTerm _
          | `Formula _ -> expr
          | `ArithTerm t ->
          match ArithTerm.destruct srk t with
            | `Var (i, _) ->
              begin
                try mk_const srk (Env.find env i)
                with Not_found -> invalid_arg "Quantifier.FineGrain.normalize: free variable"
              end
            | _ -> expr
        in
        rewrite srk ~up:rewriter t
      in
      let flatten_go comb comb_qff phis =
        let qff, phis =
          List.fold_left (fun (qff, phis) (qff', phi) ->
            (qff && qff', phi :: phis)
          ) (true, []) (List.rev_map (go env) phis)
        in
        if qff then
          let phis =
            List.map (fun phi ->
              match phi with
              | `Atom phi -> phi
              | _ -> assert false
            ) phis
          in
          (true, `Atom (comb_qff phis))
        else
          (false, comb phis)
      in
      match Formula.destruct srk phi with
      | `And phis -> flatten_go (fun phis -> `And phis) (mk_and srk) phis
      | `Or phis -> flatten_go (fun phis -> `Or phis) (mk_or srk) phis
      | `Not phi -> let qff, phi = go env phi in (qff, negate srk phi)
      | `Quantify (`Exists, name, typ, phi) ->
        let k = mk_symbol srk ~name (typ :> Syntax.typ) in
        let _, phi = go (Env.push k env) phi in
        (false, `Exists (k, phi))
      | `Quantify (`Forall, name, typ, phi) ->
        let k = mk_symbol srk ~name (typ :> Syntax.typ) in
        let _, phi = go (Env.push k env) phi in
        (false, `Forall (k, phi))
      | `Proposition (`Var i) -> (true, `Atom (mk_const srk (Env.find env i)))
      | `Atom (`Arith (`Eq, s, t)) -> (true, `Atom (mk_eq srk (mk_sub srk (go_term s) (go_term t)) zero))
      | `Atom (`Arith (`Leq, s, t)) -> (true, `Atom (mk_leq srk (mk_sub srk (go_term s) (go_term t)) zero))
      | `Atom (`Arith (`Lt, s, t)) -> (true, `Atom (mk_lt srk (mk_sub srk (go_term s) (go_term t)) zero))
      | _ -> (true, `Atom phi)
    in
    let (_, phi) = go Env.empty (eliminate_ite srk phi) in
    phi

  let pp_normal srk formatter phi =
    let rec go formatter phi =
      match phi with
      | `Forall (k, phi) ->
        Format.fprintf formatter "forall %a. %a" (pp_symbol srk) k go phi
      | `Exists (k, phi) ->
        Format.fprintf formatter "exists %a. %a" (pp_symbol srk) k go phi
      | `And phis ->
        let pp_sep formatter () = Format.fprintf formatter "/\\" in
        BatList.enum phis
        |> Format.fprintf formatter "(%a)" (SrkUtil.pp_print_enum_nobox ~pp_sep go)
      | `Or phis ->
        let pp_sep formatter () = Format.fprintf formatter "\\/" in
        BatList.enum phis
        |> Format.fprintf formatter "(%a)" (SrkUtil.pp_print_enum_nobox ~pp_sep go)
      | `Atom phi ->
        Format.fprintf formatter "%a" (Formula.pp srk) phi
    in
    Format.fprintf formatter "%a" go phi

  module CSS = struct
    type 'a ctx =
      { formula : 'a normalized_formula;
        not_formula : 'a normalized_formula; (* Negated formula *)
        mutable skeleton : Skeleton.FineGrain.t; (* skeleton for formula *)

        solver : 'a Smt.Solver.t;
        srk : 'a context;
      }

    let reset ctx =
      Smt.Solver.reset ctx.solver;
      ctx.skeleton <- Skeleton.FineGrain.SEmpty

    (* Idealy, union is only called with a non-redundant skeleton (i.e. skel \ ctx.skeleton =\= {})
       But, it will still work as an expensive no-op. 
       This assumes that ctx.solver already has (losing_formula srk ctx.skeleton) or equivalent asserted *)
    let union ctx skel =
      let srk = ctx.srk in
      let new_loss_conditions =
        Skeleton.FineGrain.union_losing_formula srk ctx.skeleton skel ctx.formula
      in
      ctx.skeleton <- Skeleton.FineGrain.union srk ctx.skeleton skel;
      Smt.Solver.add ctx.solver new_loss_conditions

(*    let initialize_pair select_term srk ?(init=Interpretation.empty srk) phi =
      let rec matrix_of = function  (* eliminates quantifiers and converts to srk formula *)
        | `Forall (_, phi) -> matrix_of phi
        | `Exists (_, phi) -> matrix_of phi
        | `Or phis -> mk_or srk (List.map matrix_of phis)
        | `And phis -> mk_and srk (List.map matrix_of phis)
        | `Atom phi -> Interpretation.substitute init phi
      in
      let phi_matrix = matrix_of phi in
      match Smt.get_model srk phi_matrix with
      | `Unsat -> `Unsat
      | `Unknown -> `Unknown
      | `Sat phi_model ->
        let phi_model =
          Interpretation.wrap srk (fun sym ->
            try Interpretation.value init sym
            with Not_found ->
              Interpretation.value phi_model sym
          )
        in
        logf "Found initial model";
        (* Create paths for sat skeleton & unsat skeleton *)
        let rec go = function
          | `Forall (k, phi) ->
            let (satp, unsatp, atoms, win) = go phi in
            let move = select_term phi_model k atoms in
            let satp = Skeleton.FineGrain.PForall (k, satp) in
            let unsatp = Skeleton.FineGrain.PExists (k, move, unsatp) in
            let atoms = Skeleton.substitute_implicant phi_model k move atoms in
            (satp, unsatp, atoms, win)
          | `Exists (k, phi) ->
            let (satp, unsatp, atoms, win) = go phi in
            let move = select_term phi_model k atoms in
            let satp = Skeleton.FineGrain.PExists (k, move, satp) in
            let unsatp = Skeleton.FineGrain.PForall (k, unsatp) in
            let atoms = Skeleton.substitute_implicant phi_model k move atoms in
            (satp, unsatp, atoms, win)
          | `And phis ->
            begin
              match List.map go phis with
              | [] -> assert false
              | (satp, unsatp, atoms, win) :: paths ->
                (* Tries to select a conjunct such that SAT's choice beats UNSAT's choice
                   Any arbitrary one works. We pick the last for ease.
                   Picking a winning conjunct ensures that atoms is not empty.
                   If none are winning just return the first conjunct. *)
                let rec select i paths satp j unsatp atoms win =
                  match paths with
                  | [] -> (satp, j, unsatp, atoms, win)
                  | (satp', unsatp', atoms', win') :: paths ->
                    if win' then
                      select (i+1) paths (satp' :: satp) i unsatp' atoms' win'
                    else
                      select (i+1) paths (satp' :: satp) j unsatp atoms win
                in
                let (satp, j, unsatp, atoms, win) =
                  select 1 paths [satp] 0 unsatp atoms win
                in
                (Skeleton.FineGrain.PAnd (List.rev satp),
                 Skeleton.FineGrain.POr (j, unsatp), atoms, win)
            end
          | `Or phis ->
            begin
              match List.map go phis with
              | [] -> assert false
              | (satp, unsatp, atoms, win) :: paths ->
                (* Tries to select a disjunct such that SAT's choice beats UNSAT's choice
                   Any arbitrary one works. We pick the last for ease.
                   Picking a winning choice ensure that atoms is not empty.
                   If none are winning the first disjunct is chosen. *)
                let rec select i paths satp j unsatp atoms win =
                  match paths with
                  | [] -> (satp, j, unsatp, atoms, win)
                  | (satp', unsatp', atoms', win') :: paths ->
                    if win' then
                      select (i+1) paths satp' i (unsatp' :: unsatp) atoms' win'
                    else
                      select (i+1) paths satp j (unsatp' :: unsatp) atoms win
                in
                let (satp, j, unsatp, atoms, win) =
                  select 1 paths satp 0 [unsatp] atoms win
                in
                (Skeleton.FineGrain.POr (j, satp),
                 Skeleton.FineGrain.PAnd (List.rev unsatp), atoms, win)
            end
          | `Atom phi ->
            (* Evaluates the atom (or ground fragment) according to the model of the matrix of phi
               If it is true, we select the atoms that hold in phi_model and return that SAT's choice won
               Otherwise, return an empty set of atoms and the fact that SAT's choice lost. *)
            if Interpretation.evaluate_formula phi_model phi then
              let phi_implicant =
                match select_implicant srk phi_model phi with
                | Some x -> x
                | None -> assert false
              in
              (Skeleton.FineGrain.PEmpty, Skeleton.FineGrain.PEmpty, phi_implicant, true)
            else
              (Skeleton.FineGrain.PEmpty, Skeleton.FineGrain.PEmpty, [], false)
        in
        let (satp, unsatp, _, win) = go phi in
        assert win; (* since phi's matrix had a model. SAT's choice should beat UNSAT's choice *)
        (* Now, we create two new contexts. One for the SAT Player's choice and one for UNSAT's choice *)
        let not_phi = negate srk phi in
        let sat_ctx =
          let skeleton = Skeleton.FineGrain.mk_path srk satp in
          let losing_condition =
            Skeleton.FineGrain.losing_formula srk skeleton phi
          in
          let solver = Smt.mk_solver srk in
          Smt.Solver.add solver [losing_condition];
          { formula = phi;
            not_formula = not_phi;
            skeleton = skeleton;
            solver = solver;
            srk = srk }
        in
        let unsat_ctx =
          let skeleton = Skeleton.FineGrain.mk_path srk unsatp in
          let losing_condition =
            Skeleton.FineGrain.losing_formula srk skeleton not_phi
          in
          let solver = Smt.mk_solver srk in
          Smt.Solver.add solver [losing_condition];
          { formula = not_phi;
            not_formula = phi;
            skeleton = skeleton;
            solver = solver;
            srk = srk }
        in
        logf "Initial SAT strategy:@\n%a"
          (Skeleton.FineGrain.pp srk) sat_ctx.skeleton;
        logf "Initial UNSAT strategy:@\n%a"
          (Skeleton.FineGrain.pp srk) unsat_ctx.skeleton;
        `Sat (sat_ctx, unsat_ctx)
*)

    let rec initialize_pair select_term srk ?(init=Interpretation.empty srk) phi =
      let not_phi = negate srk phi in
      let unsat_ctx =
        let skeleton =
          let rec go = function
            | `Forall (k, phi) ->
               let sk = mk_symbol srk ~name:(show_symbol srk k) (typ_symbol srk k) in
               Skeleton.FineGrain.SForall (k, sk, (go phi))
            | `Exists (k, phi) ->
              let move =
                match typ_symbol srk k with
                | `TyReal -> Skeleton.MReal (Linear.const_linterm QQ.zero)
                | `TyInt -> Skeleton.MInt { term = Linear.const_linterm QQ.zero;
                                            divisor = ZZ.one;
                                            offset = ZZ.zero }
                | `TyBool -> Skeleton.MBool true
                | _ -> assert false
              in
              Skeleton.FineGrain.SExists (k, Skeleton.MM.singleton move (go phi))
            | `Or phis ->
              Skeleton.FineGrain.SOr (Skeleton.FineGrain.IM.singleton 0 (go (List.hd phis)))
            | `And phis ->
              Skeleton.FineGrain.SAnd (List.map (fun phi -> mk_symbol srk ~name:"B" `TyBool, go phi) phis)
            | `Atom _ -> Skeleton.FineGrain.SEmpty
          in go not_phi
        in
        let losing_condition = Skeleton.FineGrain.losing_formula srk skeleton not_phi in
        let solver = Smt.mk_solver srk in
        Smt.Solver.add solver [losing_condition];
        BatEnum.iter (function
          | (k, `Real qv) -> Smt.Solver.add solver [mk_eq srk (mk_const srk k) (mk_real srk qv)]
          | (k, `Bool true) -> Smt.Solver.add solver [mk_const srk k]
          | (k, `Bool false) -> Smt.Solver.add solver [mk_not srk (mk_const srk k)]
          | (_, `Fun _) -> ()
        ) (Interpretation.enum init);
        { formula = not_phi;
          not_formula = phi;
          skeleton = skeleton;
          solver = solver;
          srk = srk }
      in
      match get_counter_strategy select_term ~parameters:(Some init) unsat_ctx with
      | `Unknown -> `Unknown
      | `Unsat -> `Unsat
      | `Sat skeleton ->
        let sat_ctx =
          let losing_condition = Skeleton.FineGrain.losing_formula srk skeleton phi in
          let solver = Smt.mk_solver srk in
          Smt.Solver.add solver [losing_condition];
          { formula = phi;
            not_formula = not_phi;
            skeleton = skeleton;
            solver = solver;
            srk = srk;
          }
        in
        `Sat (sat_ctx, unsat_ctx)

    (* Check if a given skeleton is winning.  If not, synthesize a
       counter-strategy. *)
    and get_counter_strategy select_term ?(parameters=None) ctx =
      let parameters =
        match parameters with
        | Some p -> p
        | None -> Interpretation.empty ctx.srk
      in
      match Smt.Solver.get_model ctx.solver with
      | `Unsat ->
        logf ~level:`trace "Winning formula is valid";
        `Unsat
      | `Unknown -> `Unknown
      | `Sat m ->
        logf ~level:`trace "Winning formula is not valid";

        (* Using the model m, synthesize a counter-strategy which beats the= 
           strategy skeleton.  This is done by traversing the skeleton: on the
           way down, we build a model of the *negation* of the formula using the
           labels on the path to the root.  On the way up, we find elimination
           terms for each universally-quantified variable using model-based
           projection. *)
        let rec counter_strategy path_model skeleton not_phi =
          let open Skeleton in
          let open FineGrain in
          logf ~level:`trace "Path model: %a" Interpretation.pp path_model;
          match not_phi, skeleton with
          | `Exists (k', psi), SForall (k, sk, t) ->
            assert (k' = k);
            let path_model =
              Interpretation.add k (Interpretation.value m sk) path_model
            in
            logf ~level:`trace "Forall %a (%a)"
              (pp_symbol ctx.srk) k
              (pp_symbol ctx.srk) sk;
            let (win, counter_phi, counter_skel) =
              counter_strategy path_model t psi
            in
            (* win ==> counter_skel wins against skeleton /\ (path_model |= /\ counter_phi) *)
            if win then
              begin
                let move = select_term path_model k counter_phi in
                logf ~level:`trace "Found move: %a = %a"
                  (pp_symbol ctx.srk) k
                  (Skeleton.pp_move ctx.srk) move;
                let counter_phi =
                  substitute_implicant path_model k move counter_phi
                in
                (true, counter_phi, SExists (k, MM.singleton move counter_skel))
              end
            else (false, [], SEmpty)
          | `Forall (k', psi), SExists (k, mm) ->
            assert (k' = k);
            (* we keep the invariant that counter_paths wins against all moves already processed for any
               starting state satisfying counter_phi (path_model being one such starting state *)
            let module Set = Expr.Set in
            let moves = MM.enum mm in
            let rec go counter_phi counter_skel =
              match BatEnum.get moves with
              | None -> (true, Set.elements counter_phi, counter_skel)  (* counter_skel wins against all possible moves *)
              | Some (move, skeleton) ->
                let path_model =
                  match move with
                  | Skeleton.MBool bool_val ->
                    Interpretation.add_bool k bool_val path_model
                  | _ ->
                    let mv =
                      Skeleton.evaluate_move (Interpretation.real path_model) move
                    in
                    Interpretation.add_real k mv path_model
                in
                let (win, counter_phi', counter_skel') =
                  counter_strategy path_model skeleton psi
                in
                if win then
                  let counter_phi' = Set.of_list (Skeleton.substitute_implicant path_model k move counter_phi') in
                  let counter_skel' = SForall (k, mk_symbol ctx.srk ~name:(show_symbol ctx.srk k) (typ_symbol ctx.srk k), counter_skel') in
                  go (Set.union counter_phi' counter_phi) (union ctx.srk counter_skel counter_skel')
                else
                  (false, [], SEmpty)
            in go Set.empty SEmpty
          | `And sub_phis, SOr im ->
            let module Set = Expr.Set in
            let rec go i phis counter_phi counter_skels =
              match phis with
              | [] ->
                let counter_phi = Set.elements counter_phi in
                (true, counter_phi, SAnd (List.rev counter_skels))
              | phi :: phis ->
                match IM.find_opt i im with
                | None -> (* find any strategy *)
                  let skel =
                    match initialize_pair select_term ctx.srk ~init:path_model phi with
                    | `Unknown -> assert false
                    | `Sat (sat_ctx, _) -> sat_ctx.skeleton
                    | `Unsat ->
                      match initialize_pair select_term ctx.srk ~init:path_model (negate ctx.srk phi) with
                      | `Sat (_, unsat_ctx) -> unsat_ctx.skeleton
                      | _ -> assert false
                  in
                  go (i + 1) phis counter_phi ((mk_symbol ctx.srk ~name:"B" `TyBool, skel) :: counter_skels)
                | Some skeleton ->
                  let (win, counter_phi', counter_skel) = counter_strategy path_model skeleton phi in
                  if win then
                    let counter_skel = (mk_symbol ctx.srk ~name:"B" `TyBool, counter_skel) in
                    go (i + 1) phis (Set.union (Set.of_list counter_phi') counter_phi) (counter_skel :: counter_skels)
                  else
                    (false, [], SEmpty)
            in go 0 sub_phis Set.empty []
          | `Or sub_phis, SAnd sub_skels ->
            (* choose first winning sub counter-strategy
               Other possible options: choose randomly amongst any winning substrategy
                                       take union of all winning sub-strategies  *)
            let rec go i phis skels =
              match phis, skels with
              | [], [] -> (false, [], SEmpty)
              | phi :: phis, (_, skel) :: skels ->
                let (win, counter_phi, counter_skel) =
                  counter_strategy path_model skel phi
                in
                if win then
                  (true, counter_phi, SOr (IM.singleton i counter_skel))
                else
                  go (i + 1) phis skels
              | _, _ -> assert false
            in go 0 sub_phis sub_skels
          | `Atom phi, SEmpty ->
            let win = Interpretation.evaluate_formula path_model phi in
            if win then
              let phi_implicant =
                match select_implicant ctx.srk path_model phi with
                | Some x -> x
                | None -> assert false
              in
              (true, phi_implicant, SEmpty)
            else
              (false, [], SEmpty)
          | _, _ -> assert false
        in
        let (win, _, counter_skel) =
          counter_strategy parameters ctx.skeleton ctx.not_formula
        in
        if not win then begin
          Format.printf "Trying to counter %a\n" (Skeleton.FineGrain.pp ctx.srk) ctx.skeleton;
          Format.printf "%s\n" (Smt.Solver.to_string ctx.solver);
          Format.printf "%a\n" (Formula.pp ctx.srk) (Skeleton.FineGrain.losing_formula ctx.srk ctx.skeleton ctx.formula);
          Format.printf "with model: %a\n" Interpretation.pp m;
          Format.printf "%a\n" (pp_normal ctx.srk) ctx.not_formula;
          Format.printf "Attempted counter skeleton: %a\n" (Skeleton.FineGrain.pp ctx.srk) counter_skel
        end;
        assert win;
        `Sat counter_skel

    let is_sat select_term sat_ctx unsat_ctx =
      let round = ref 0 in
      let old_paths = ref (-1) in
      let rec is_sat () =
        incr round;
        logf ~level:`trace ~attributes:[`Blue;`Bold]
          "Round %d: Sat [%d/%d], Unsat [%d/%d]"
          (!round)
          (Skeleton.FineGrain.size sat_ctx.skeleton)
          (Skeleton.FineGrain.nb_paths sat_ctx.skeleton)
          (Skeleton.FineGrain.size unsat_ctx.skeleton)
                (Skeleton.FineGrain.nb_paths unsat_ctx.skeleton);
        let paths = Skeleton.FineGrain.nb_paths sat_ctx.skeleton in
        assert (paths > !old_paths);
        old_paths := paths;
        logf ~attributes:[`Blue;`Bold] "Checking if SAT wins (%d)"
          (Skeleton.FineGrain.nb_paths sat_ctx.skeleton);
        match get_counter_strategy select_term sat_ctx with
        | `Sat skel -> union unsat_ctx skel; is_unsat ()
        | `Unsat -> `Sat sat_ctx.skeleton
        | `Unknown -> `Unknown
      and is_unsat () =
        logf ~attributes:[`Blue;`Bold] "Checking if UNSAT wins (%d)"
          (Skeleton.FineGrain.nb_paths unsat_ctx.skeleton);
        match get_counter_strategy select_term unsat_ctx with
        | `Sat skel -> union sat_ctx skel; is_sat ()
        | `Unsat -> `Unsat unsat_ctx.skeleton
        | `Unknown -> `Unknown
      in
      is_sat ()
  end

  let simsat_core srk phi =
    let select_term model x phi =
      match typ_symbol srk x with
      | `TyInt -> Skeleton.MInt (select_int_term srk model x phi)
      | `TyReal -> Skeleton.MReal (select_real_term srk model x phi)
      | `TyBool -> Skeleton.MBool (Interpretation.bool model x)
      | `TyFun (_, _) -> assert false
      | `TyArr -> assert false
    in
    match CSS.initialize_pair select_term srk phi with
    | `Unsat ->
      (* matrix is unsat -> any unsat strategy is winning *)
      let open Skeleton.FineGrain in
      let rec go = function
        | `Forall (k, psi) ->
          let sk = mk_symbol srk ~name:(show_symbol srk k) (typ_symbol srk k) in
          SForall (k, sk, go psi)
        | `Exists (k, psi) ->
          let move =
            match typ_symbol srk k with
            | `TyReal -> Skeleton.MReal (Linear.const_linterm QQ.zero)
            | `TyInt -> Skeleton.MInt { term = Linear.const_linterm QQ.zero;
                                        divisor = ZZ.one;
                                        offset = ZZ.zero }
            | `TyBool -> Skeleton.MBool true
            | _ -> assert false
          in
          SExists (k, Skeleton.MM.singleton move (go psi))
        | `And phis -> SAnd (List.map (fun phi -> (mk_symbol srk ~name:"B" `TyBool, go phi)) phis)
        | `Or phis -> SOr (IM.singleton 0 (go (List.hd phis)))
        | `Atom _ -> SEmpty
      in
      `Unsat (go phi)
    | `Unknown -> `Unknown
    | `Sat (sat_ctx, unsat_ctx) ->
      CSS.reset unsat_ctx;
      CSS.is_sat select_term sat_ctx unsat_ctx

  let simsat_forward_core srk phi =
    let select_term model x atoms =
      match typ_symbol srk x with
      | `TyInt -> Skeleton.MInt (select_int_term srk model x atoms)
      | `TyReal -> Skeleton.MReal (select_real_term srk model x atoms)
      | `TyBool -> Skeleton.MBool (Interpretation.bool model x)
      | `TyFun (_, _) -> assert false
      | `TyArr -> assert false
    in

    (* If SAT plays first, check satisfiability of the negated sentence instead,
       then negate the result. We may now assume that UNSAT always plays first. *)
    let (phi, negate) =
      match phi with
      | `Exists _ | `Or _ -> (negate srk phi, true)
      | _ -> (phi, false)
    in
    match CSS.initialize_pair select_term srk phi with
    | `Unsat ->
      (* Matrix is unsat -> any unsat strategy is winning *)
      let open Skeleton.FineGrain in
      let rec go = function
        | `Forall (k, psi) ->
          let sk = mk_symbol srk ~name:(show_symbol srk k) (typ_symbol srk k) in
          SForall (k, sk, go psi)
        | `Exists (k, psi) ->
          let move =
            match typ_symbol srk k with
            | `TyReal -> Skeleton.MReal (Linear.const_linterm QQ.zero)
            | `TyInt -> Skeleton.MInt { term = Linear.const_linterm QQ.zero;
                                        divisor = ZZ.one;
                                        offset = ZZ.zero }
            | `TyBool -> Skeleton.MBool true
            | _ -> assert false
          in
          SExists (k, Skeleton.MM.singleton move (go psi))
        | `And phis -> SAnd (List.map (fun phi -> (mk_symbol srk ~name:"B" `TyBool, go phi)) phis)
        | `Or phis -> SOr (IM.singleton 0 (go (List.hd phis)))
        | `Atom _ -> SEmpty
      in
      if negate then `Sat (go phi)
      else `Unsat (go phi)

    | `Unknown -> `Unknown
    | `Sat (sat_ctx, _) ->
      let assert_param_constraints ctx parameter_interp =
        let open CSS in
        BatEnum.iter (function
            | (k, `Real qv) ->
              Smt.Solver.add ctx.solver [mk_eq srk (mk_const srk k) (mk_real srk qv)]
            | (k, `Bool false) ->
              Smt.Solver.add ctx.solver [mk_not srk (mk_const srk k)]
            | (k, `Bool true) ->
              Smt.Solver.add ctx.solver  [mk_const srk k]
            | (_, `Fun _) -> ())
          (Interpretation.enum parameter_interp)
      in
      let mk_unsat_ctx skeleton parameter_interp phi not_phi =
        let open CSS in
        let lose =
          Skeleton.FineGrain.losing_formula srk skeleton not_phi
        in
        let ctx =
          { formula = not_phi;
            not_formula = phi;
            skeleton = skeleton;
            solver = Smt.mk_solver srk;
            srk = srk }
        in
        Smt.Solver.add ctx.solver [lose];
        assert_param_constraints ctx parameter_interp;
        ctx
      in

      (* Peel leading SAT choices (existentials and disjunctions) off of a skeleton.
         Fails if there is more than one move for a SAT choice in the prefix.
         We also return the sub formula, and it's negation. *)
      let rec sat_prefix skel phi not_phi =
        match skel, phi, not_phi with
        | Skeleton.FineGrain.SExists (k, mm), `Forall (_, phi), `Exists (_, not_phi) ->
          begin match BatList.of_enum (Skeleton.MM.enum mm) with
          | [(move, skeleton)] ->
            let (ex_pre, sub_skeleton, phi, not_phi) = sat_prefix skeleton phi not_phi in
            ((k, move)::ex_pre, sub_skeleton, phi, not_phi)
          | _ -> assert false
          end
        | Skeleton.FineGrain.SOr im, `And phis, `Or not_phis ->
          begin match BatList.of_enum (Skeleton.FineGrain.IM.enum im) with
          | [(i, skeleton)] -> sat_prefix skeleton (List.nth phis i) (List.nth not_phis i)
          | _ -> assert false
          end
        | Skeleton.FineGrain.SExists _, _, _ | Skeleton.FineGrain.SOr _, _, _ ->
          assert false
        | _ -> ([], skel, phi, not_phi)
      in

      (* Compute a winning strategy for the remainder of the game, after the
         prefix play determined by parameter_interp.  Skeleton is an initial
         candidate strategy for one of the players, which begins with
         universals. *)
      let rec solve_game polarity param_interp ctx =
        logf ~attributes:[`Green] "Solving game %s (%d/%d)"
          (if polarity then "SAT" else "UNSAT")
          (Skeleton.FineGrain.nb_paths ctx.CSS.skeleton)
          (Skeleton.FineGrain.size ctx.CSS.skeleton);
        logf ~level:`trace "Parameters: %a" Interpretation.pp param_interp;
        match CSS.get_counter_strategy select_term ~parameters:(Some param_interp) ctx with
        | `Unknown -> `Unknown
        | `Unsat ->
          (* No counter-strategy to the strategy of the active player => active
             player wins *)
          `Sat ctx.CSS.skeleton
        | `Sat unsat_skel -> (* inactive player has a counter strategy *)
          let (ex_pre, sub_skeleton, phi, not_phi) = sat_prefix unsat_skel ctx.CSS.formula ctx.CSS.not_formula in
          let param_interp =
            List.fold_left (fun interp (k, move) ->
                match move with
                | Skeleton.MBool bv -> Interpretation.add_bool k bv interp
                | move ->
                  Interpretation.add_real
                    k
                    (Skeleton.evaluate_move (Interpretation.real interp) move)
                    interp
              ) param_interp ex_pre
          in
          let sub_ctx = mk_unsat_ctx sub_skeleton param_interp phi not_phi in
          match solve_game (not polarity) param_interp sub_ctx with
          | `Unknown -> `Unknown
          | `Sat skeleton ->
            (* Inactive player wins *)
            let skeleton =
              let rec go = function
                | Skeleton.FineGrain.SExists (k, mm) ->
                  begin match BatList.of_enum (Skeleton.MM.enum mm) with
                  | [(move, skel)] ->
                    let mm = Skeleton.MM.add move (go skel) Skeleton.MM.empty in
                    Skeleton.FineGrain.SExists (k, mm)
                  | _ -> assert false
                  end
                | Skeleton.FineGrain.SOr im ->
                  begin match BatList.of_enum (Skeleton.FineGrain.IM.enum im) with
                  | [(i, skel)] ->
                    let im = Skeleton.FineGrain.IM.add i (go skel) Skeleton.FineGrain.IM.empty in
                    Skeleton.FineGrain.SOr im
                  | _ -> assert false
                  end
                | _ -> skeleton
              in go unsat_skel
            in
            `Unsat skeleton
          | `Unsat skeleton' ->
            (* There is a counter-strategy for the strategy of the inactive
               player => augment strategy for the active player & try again *)
            let open CSS in
            let skeleton = (* compute union of ctx.skeleton and skeleton' that starts after unsat_skel's sat_prefix *)
              let rec go sat_skel unsat_skel =
                match sat_skel, unsat_skel with
                | Skeleton.FineGrain.SForall (k, sk, sat_skel), Skeleton.FineGrain.SExists (_, mm) ->
                  begin match BatList.of_enum (Skeleton.MM.enum mm) with
                  | [(_, unsat_skel)] ->
                    Skeleton.FineGrain.SForall (k, sk, go sat_skel unsat_skel)
                  | _ -> assert false
                  end
                | Skeleton.FineGrain.SAnd sat_skels, Skeleton.FineGrain.SOr im ->
                  begin match BatList.of_enum (Skeleton.FineGrain.IM.enum im) with
                  | [(i, unsat_skel)] ->
                    Skeleton.FineGrain.SAnd (List.mapi (fun j (b, sat_skel) ->
                                                         if i = j then
                                                           (b, go sat_skel unsat_skel)
                                                         else
                                                           (b, sat_skel)
                                                       ) sat_skels)
                  | _ -> assert false
                  end
                | Skeleton.FineGrain.SForall _, _ | Skeleton.FineGrain.SAnd _, _ -> assert false
                | _, _ -> Skeleton.FineGrain.union srk sat_skel skeleton'
              in go ctx.skeleton unsat_skel
            in
            Skeleton.FineGrain.union_losing_formula srk ctx.skeleton skeleton ctx.formula
            |> List.map (fun phi -> Interpretation.substitute param_interp phi)
            |> Smt.Solver.add ctx.solver;
            ctx.skeleton <- skeleton;
            solve_game polarity param_interp ctx
      in
      match solve_game true (Interpretation.empty srk) sat_ctx with
      | `Unknown -> `Unknown
      | `Sat skeleton -> if negate then `Unsat skeleton else `Sat skeleton
      | `Unsat skeleton -> if negate then `Sat skeleton else `Unsat skeleton

  let simsat srk phi =
    let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
    let phi =
      normalize srk (miniscope srk phi)
      |> Symbol.Set.fold (fun sym phi ->
           `Exists (sym, phi)
         ) constants
    in
    match simsat_core srk phi with
    | `Sat _ -> `Sat
    | `Unsat _ -> `Unsat
    | `Unknown -> `Unknown

  let simsat_forward srk phi =
    let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
    let phi =
      normalize srk (miniscope srk phi)
      |> Symbol.Set.fold (fun sym phi ->
           `Exists (sym, phi)
         ) constants
    in
    match simsat_forward_core srk phi with
    | `Sat _ -> `Sat
    | `Unsat _ -> `Unsat
    | `Unknown -> `Unknown

  let maximize _ _ _ = failwith "Quantifier.FineGrainStrategyImprovement.maximize not implemented"
  let easy_sat _ _ = failwith "Quantifier.FineGrainStrategyImprovement.easy_sat not implemented"

  type 'a skeleton = 'a fg_skeleton

  let pp_skeleton srk formatter skel =
    let open Format in
    let pp_sep formatter () = fprintf formatter "@;" in
    let rec pp formatter = function
      | `Forall (k, sub_skel) ->
        fprintf formatter "@;  @[<v 0>forall %a. %a@]"
          (pp_symbol srk) k
          pp sub_skel
      | `Exists (k, moves) ->
        let pp_elt formatter (expr, sub_skel) =
          fprintf formatter "(%a |-> %a)%a"
            (pp_symbol srk) k
            (Expr.pp srk) expr
            pp sub_skel
        in
        fprintf formatter "@;  @[<v 0>exists %a. %a@]"
          (pp_symbol srk) k
          (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt)
          (BatList.enum moves)
      | `Or moves ->
        let pp_elt formatter (ind, sub_skel) =
          fprintf formatter "or%d%a"
            ind
            pp sub_skel
        in
        fprintf formatter "@;  @[<v 0>%a@]"
          (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt)
          (BatList.enum moves)
      | `And sub_skels ->
        let pp_elt formatter sub_skel =
          fprintf formatter "and%a"
            pp sub_skel
        in
        fprintf formatter "@;  @[<v 0>%a@]"
          (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt)
          (BatList.enum sub_skels)
      | `Empty -> ()
    in
    Format.fprintf formatter "%a" pp skel

  let show_skeleton srk = SrkUtil.mk_show (pp_skeleton srk)

  let winning_skeleton srk phi =
    let rec rename subst_map skel =
      let open Skeleton.FineGrain in
      match skel with
      | SForall (k, sk, sub_skel) ->
        let subst_map = Symbol.Map.add sk (mk_const srk k) subst_map in
        `Forall (k, rename subst_map sub_skel)
      | SExists (k, mm) ->
        let moves =
          Skeleton.MM.enum mm
          |> BatList.of_enum
          |> List.map (fun (move, sub_skel) ->
            (substitute_map srk subst_map (
              match move with
              | Skeleton.MInt vt -> (term_of_virtual_term srk vt :> ('a, typ_fo) expr)
              | Skeleton.MReal linterm -> (of_linterm srk linterm :> ('a, typ_fo) expr)
              | Skeleton.MBool true -> (mk_true srk :> ('a, typ_fo) expr)
              | Skeleton.MBool false -> (mk_false srk :> ('a, typ_fo) expr)
              ), rename subst_map sub_skel)
          )
        in `Exists (k, moves)
      | SAnd sub_skels -> `And (List.map (fun (_, skel) -> rename subst_map skel) sub_skels)
      | SOr im ->
        let moves =
          IM.enum im
          |> BatList.of_enum
          |> List.map (fun (ind, sub_skel) ->
            (ind, rename subst_map sub_skel)
          )
        in `Or moves
      | SEmpty -> `Empty
    in
    match simsat_core srk phi with
    | `Sat skel -> `Sat (rename Symbol.Map.empty skel)
    | `Unsat skel -> `Unsat (rename Symbol.Map.empty skel)
    | `Unknown -> `Unknown

  type 'a move = [ `Forall of symbol
                 | `Exists of symbol * ('a, typ_fo) expr
                 | `Or of int
                 | `And of int ]

  type 'a strategy =
    | Forall of symbol * 'a strategy
    | Exists of symbol * (('a formula * ('a, typ_fo) expr * 'a strategy) list)
    | Or of ('a formula * int * 'a strategy) list
    | And of 'a strategy list
    | Empty

  let pp_strategy srk formatter strat =
    let open Format in
    let pp_sep formatter () = fprintf formatter "@;" in
    let rec pp formatter = function
      | Forall (k, sub_strat) ->
        fprintf formatter "@;  @[<v 0>forall %a. %a@]"
          (pp_symbol srk) k
          pp sub_strat
      | Exists (k, moves) ->
        let pp_elt formatter (guard, expr, sub_strat) =
          fprintf formatter "%a --> (%a |-> %a)%a"
            (Formula.pp srk) guard
            (pp_symbol srk) k
            (Expr.pp srk) expr
            pp sub_strat
        in
        fprintf formatter "@;  @[<v 0>exists %a. %a@]"
          (pp_symbol srk) k
          (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt)
          (BatList.enum moves)
      | Or moves ->
        let pp_elt formatter (guard, ind, sub_strat) =
          fprintf formatter "%a --> or%d%a"
            (Formula.pp srk) guard
            ind
            pp sub_strat
        in
        fprintf formatter "@;  @[<v 0>%a@]"
          (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt)
          (BatList.enum moves)
      | And sub_strats ->
        let pp_elt formatter (ind, sub_strat) =
          fprintf formatter "and%d%a"
            ind
            pp sub_strat
        in
        fprintf formatter "@;  @[<v 0>%a@]"
          (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt)
          (BatList.enum sub_strats
           |> BatEnum.mapi (fun i strat -> (i, strat)))
      | Empty -> ()
    in
    Format.fprintf formatter "%a" pp strat

  let show_strategy srk = SrkUtil.mk_show (pp_strategy srk)

  let extract_strategy srk skeleton phi =
    let module DA = BatDynArray in
    (* by vars, we mean which skolemn constants the relation of
       each node can reference. This is the same rule as tree interpolants.
       It is the intersection of the vars of it's decsendants and non-decsendants *)
    let vars = DA.create () in
    let children = DA.create () in
    let is_union = DA.create () in      (* is_union[i] <==> i is an AND node *)
    let labels = Hashtbl.create 991 in  (* only leaves (atoms) have a non-T label *)
    let module Set = Symbol.Set in
    (* We will associate an int id for each sub-path of the skeleton
       This is implemented implicitly through i. *)
    let rec go i skeleton phi subst =
      DA.add vars Set.empty;
      DA.add children [];
      DA.add is_union false;
      let open Skeleton.FineGrain in
      match skeleton, phi with
      | SForall (k, sk, sub_skel), `Forall (k', psi) ->
        assert (k = k');
        let sk_const = mk_const srk sk in
        let subst expr =
          subst (substitute_const srk
                  (fun p -> if p = k then sk_const else mk_const srk p)
                 expr)
        in
        DA.set children i [i + 1];
        let (max_id, psi_vars) = go (i + 1) sub_skel psi subst in
        DA.set vars i psi_vars;
        (max_id, psi_vars)
      | SExists (k, mm), `Exists (k', psi) ->
        assert (k = k');
        let (max_id, children_vars) =
          Skeleton.MM.enum mm
          |> BatEnum.fold (fun (id, vars) (move, sub_skel) ->
               let subst expr =
                 subst (Skeleton.substitute srk k move expr)
               in
               let (max_id, sub_vars) =
                 DA.set children i ((id + 1)::(DA.get children i));
                 go (id + 1) sub_skel psi subst
               in
               (max_id, Set.union sub_vars vars)
             ) (i, Set.empty)
        in
        DA.set children i (List.rev (DA.get children i));
        DA.set vars i children_vars;
        (max_id, children_vars)
      | SAnd sub_skels, `And sub_phis ->
        let (max_id, children_vars) =
          List.fold_left2 (fun (id, vars) (_, sub_skel) sub_phi ->
            let (max_id, sub_vars) =
              DA.set children i ((id + 1)::(DA.get children i));
              go (id + 1) sub_skel sub_phi subst
            in
            (max_id, Set.union sub_vars vars)
          ) (i, Set.empty) sub_skels sub_phis
        in
        DA.set children i (List.rev (DA.get children i));
        DA.set is_union i true;
        DA.set vars i children_vars;
        (max_id, children_vars)
      | SOr im, `Or sub_phis ->
        let (max_id, children_vars) =
          IM.enum im
          |> BatEnum.fold (fun (id, vars) (ind, sub_skel) ->
               let (max_id, sub_vars) =
                 DA.set children i ((id + 1)::(DA.get children i));
                 go (id + 1) sub_skel (List.nth sub_phis ind) subst
               in
               (max_id, Set.union sub_vars vars)
             ) (i, Set.empty)
        in
        DA.set children i (List.rev (DA.get children i));
        DA.set vars i children_vars;
        (max_id, children_vars)
      | SEmpty, `Atom phi ->
        Hashtbl.add labels i (mk_not srk (subst phi));
        let phi_vars = symbols (subst phi) in
        DA.set vars i phi_vars;
        (i, phi_vars)
      | _, _ -> 
       logf ~level:`warn "\n%a\n%a" (pp_normal srk) phi (pp srk) skeleton; assert false
    in
    ignore (go 0 skeleton phi (fun expr -> expr));
    (* We've so far computed the variables of a "nodes" descendants
       now, we will intersect with the variables of it's non-descendants
         on the way down, we will compute the non-descendant variables,
         on the way up, we will compute the system of horn-clauses *)
    let relation = Hashtbl.create 991 in (* Using hashtbl rather than Array allows us to iterate over children in any order *)
    let module CHC = SrkZ3.CHC in
    let solver = CHC.mk_solver srk in
    let fresh _ =
      let ind = ref (-1) in
      let rev_subs = DA.create () in
      let memo =
        Memo.memo (fun sym ->
          match typ_symbol srk sym with
          | `TyInt  -> incr ind; DA.add rev_subs sym; mk_var srk (!ind) `TyInt
          | `TyReal -> incr ind; DA.add rev_subs sym; mk_var srk (!ind) `TyReal
          | `TyBool -> incr ind; DA.add rev_subs sym; mk_var srk (!ind) `TyBool
          | _ -> mk_const srk sym)
      in
      (rev_subs, memo)
    in
    let rec go i non_vars =
      let (rev_subst, fresh) = fresh () in
      DA.set vars i (Set.inter non_vars (DA.get vars i));
      let non_vars = DA.get vars i in
      let hypothesis =
        match DA.get children i with
        | [] -> Hashtbl.find labels i
        | children ->
          let rec go_child pre acc = function
            | [] -> acc
            | child :: rest ->
              let non_vars =
                List.fold_left (fun nv sibling ->
                  Set.union nv (DA.get vars sibling)
                ) non_vars (List.append pre rest)
              in
              go_child (child :: pre) ((go child non_vars) :: acc) rest
          in
          go_child [] [] children
          |> (if DA.get is_union i then mk_or srk else mk_and srk)
      in
      let vars_typ =
        List.map (fun sym ->
          match typ_symbol srk sym with
          | `TyInt -> `TyInt
          | `TyReal -> `TyReal
          | `TyBool -> `TyBool
          | _ -> assert false
        ) (Set.elements non_vars)
      in
      let vars_const = List.map (fun sym -> mk_const srk sym) (Set.elements non_vars) in
      let rel_sym = mk_symbol srk (`TyFun (vars_typ, `TyBool)) in
      Hashtbl.add relation i (rel_sym, rev_subst);
      let conclusion = mk_app srk rel_sym vars_const in
      CHC.register_relation solver rel_sym;
      CHC.add_rule solver (substitute_const srk fresh hypothesis)
                          (substitute_const srk fresh conclusion);
      logf ~level:`trace "%a <== %a" (Formula.pp srk) conclusion (Formula.pp srk) hypothesis;
      conclusion
    in
    let root = go 0 Set.empty in
    let (_, fresh) = fresh () in
    CHC.add_rule solver (substitute_const srk fresh root) (mk_false srk);
    logf ~level:`trace "false <== %a" (Formula.pp srk) root;
    match CHC.check solver with
    | `Sat ->
      let solution = CHC.get_solution solver in
      let guard i =
        let (rel_sym, rev_subst) = Hashtbl.find relation i in
        let subst = substitute srk (fun (i, _) -> mk_const srk (DA.get rev_subst i)) in
        subst (mk_not srk (solution rel_sym))
      in
      let rec go i skel subst_map =
        let open Skeleton.FineGrain in
        match skel with
        | SForall (k, sk, sub_skel) ->
          let subst_map = Symbol.Map.add sk (mk_const srk k) subst_map in
          Forall (k, go (i + 1) sub_skel subst_map)
        | SExists (k, mm) ->
          let moves =
            Skeleton.MM.enum mm
            |> BatList.of_enum
            |> List.map2 (fun id (move, sub_skel) ->
                 (substitute_map srk subst_map (guard id),
                   substitute_map srk subst_map (match move with
                    | Skeleton.MInt vt -> (term_of_virtual_term srk vt :> ('a, typ_fo) expr)
                    | Skeleton.MReal linterm -> (of_linterm srk linterm :> ('a, typ_fo) expr)
                    | Skeleton.MBool true -> (mk_true srk :> ('a, typ_fo) expr)
                    | Skeleton.MBool false -> (mk_false srk :> ('a, typ_fo) expr)
                   ), go id sub_skel subst_map
                 )
               ) (DA.get children i)
          in Exists (k, moves)
        | SAnd sub_skels ->
          And (List.map2 (fun id (_, skel) -> go id skel subst_map) (DA.get children i) sub_skels)
        | SOr im ->
          let moves =
            IM.enum im
            |> BatList.of_enum
            |> List.map2 (fun id (ind, sub_skel) ->
                 (substitute_map srk subst_map (guard id), ind, (go id sub_skel subst_map))
               ) (DA.get children i)
          in Or moves
        | SEmpty -> Empty
      in go 0 skeleton Symbol.Map.empty
    | `Unsat -> assert false
    | `Unknown -> failwith "Quantifier.FineGrain.extract_strategy : CHC solver failed to solve system"

  let winning_strategy srk phi =
    match simsat_core srk phi with
    | `Sat skeleton ->
      logf "Formula is SAT.  Extracting strategy.";
      `Sat (extract_strategy srk skeleton phi)
    | `Unsat skeleton ->
      logf "Formula is UNSAT.  Extracting strategy.";
      `Unsat (extract_strategy srk skeleton (negate srk phi))
    | `Unknown -> `Unknown

  let check_strategy srk phi strategy =
    (* go strat strategy computes a formula whose models correspond to
       winning plays of phi where SAT plays according to strat *)
    let rec go phi strat subst =
      match phi, strat with
      | `Forall (k, psi), Forall (k', strat) ->
        assert (k = k'); go psi strat subst
      | `Exists (k, psi), Exists (k', moves) ->
        assert (k = k');
        let subst replacement expr =
          subst (substitute_const srk
            (fun p -> if p = k then replacement else mk_const srk p)
            expr)
        in
        List.fold_left (fun phis (guard, move, sub_strat) ->
          (mk_and srk [guard; go psi sub_strat (subst move)]) :: phis
        ) [] moves |> mk_or srk
      | `And phis, And sub_strats ->
        List.map2 (fun phi sub_strat ->
          go phi sub_strat subst 
        ) phis sub_strats |> mk_and srk
      | `Or phis, Or moves ->
        List.fold_left (fun psis (guard, ind, sub_strat) ->
          (mk_and srk [guard; go (List.nth phis ind) sub_strat subst]) :: psis
        ) [] moves |> mk_or srk
      | `Atom phi, Empty -> subst phi
      | _, _ -> assert false
    in
    let losing_plays = mk_not srk (go phi strategy (fun expr -> expr)) in
    logf ~level:`trace "Formula to check: %a" (Formula.pp srk) losing_plays;
    Smt.is_sat srk losing_plays = `Unsat

end

exception Unknown
let qe_mbp srk phi =
  let (qf_pre, phi) = normalize srk phi in
  let phi = eliminate_ite srk phi in
  let exists x phi =
    let solver = Smt.mk_solver srk in
    let disjuncts = ref [] in
    let rec loop () =
      match Smt.Solver.get_model solver with
      | `Sat m ->
        let implicant =
          match select_implicant srk m phi with
          | Some x -> x
          | None -> assert false
        in

        let vt = mbp_virtual_term srk m x implicant in
        let psi = virtual_substitution srk x vt phi in
        disjuncts := psi::(!disjuncts);
        Smt.Solver.add solver [mk_not srk psi];
        loop ()
      | `Unsat -> mk_or srk (!disjuncts)
      | `Unknown -> raise Unknown
    in
    Smt.Solver.add solver [phi];
    loop ()
  in
  List.fold_right
    (fun (qt, x) phi ->
       match qt with
       | `Exists ->
         exists x (snd (normalize srk phi))
       | `Forall ->
         mk_not srk (exists x (snd (normalize srk (mk_not srk phi)))))
    qf_pre
    phi

(* Given a set of dimensions to project and a set of equations, orient
   the equations into a set rewrite rules of the form (a * x) -> t *)
let _orient project eqs =
  let simplify vec =
    let gcd = (* GCD of coefficients *)
      BatEnum.fold (fun gcd (a, _) -> ZZ.gcd gcd a) ZZ.zero (ZZVector.enum vec)
    in
    ZZVector.map (fun _ a -> ZZ.div a gcd) vec
  in
  (* Replace a*dim -> rhs in vec.  a must be positive. *)
  let substitute (a, dim) rhs vec =
    let (b,vec') = ZZVector.pivot dim vec in
    if ZZ.equal ZZ.zero b then
      vec
    else
      let lcm = ZZ.abs (ZZ.lcm a b) in
      let rhs = ZZVector.scalar_mul (ZZ.div lcm a) rhs in
      let vec' = ZZVector.scalar_mul (ZZ.div lcm b) vec' in
      simplify (ZZVector.add rhs vec')
  in
  (* Simplify equations *)
  let eqs =
    eqs
    |> List.map (fun vec ->
           let den = common_denominator vec in
           V.enum vec
           /@ (fun (scalar, dim) ->
             match QQ.to_zz (QQ.mul (QQ.of_zz den) scalar) with
             | Some z -> (z, dim)
             | None -> assert false)
           |> ZZVector.of_enum
           |> simplify)
  in
  let rec go eqs oriented =
    (* Find orientation among all equations that minimizes the leading coefficient *)
    let champion =
      List.fold_left (fun champion vec ->
          BatEnum.fold (fun champion (a, dim) ->
              if  IntSet.mem dim project then
                let candidate =
                  if ZZ.lt a ZZ.zero then
                    Some (ZZ.negate a, dim, snd (ZZVector.pivot dim vec))
                  else
                    Some (a, dim, ZZVector.negate (snd (ZZVector.pivot dim vec)))
                in
                match champion with
                | Some (b, _, _) ->
                   if ZZ.lt (ZZ.abs a) b then candidate
                   else champion
                | None -> candidate
              else
                champion)
            champion
            (ZZVector.enum vec))
        None
        eqs
    in
    match champion with
    | Some (a, dim, rhs) ->
       let reduced_eqs =
         List.filter_map (fun vec ->
             let vec' = substitute (a, dim) rhs vec in
             if ZZVector.equal ZZVector.zero vec' then
               None
             else
               Some vec')
           eqs
       in
       go reduced_eqs ((a, dim, rhs)::oriented)
    | None -> (List.rev oriented, eqs)
  in
  go eqs []

let mbp ?(dnf=false) srk exists phi =
  let phi =
    eliminate_ite srk phi
    |> rewrite srk
         ~down:(nnf_rewriter srk)
         ~up:(SrkSimplify.simplify_terms_rewriter srk)
  in
  let project =
    Symbol.Set.filter (not % exists) (symbols phi)
  in
  let project_int =
    Symbol.Set.fold (fun s set ->
        IntSet.add (Linear.dim_of_sym s) set)
      project
      IntSet.empty
  in
  let solver = Smt.mk_solver ~theory:"QF_LIA" srk in
  let disjuncts = ref [] in
  let is_true phi =
    match Formula.destruct srk phi with
    | `Tru -> true
    | _ -> false
  in
  (* Sequentially compose [subst] with the substitution [symbol -> term] *)
  let seq_subst symbol term subst =
    let subst_symbol =
      substitute_const srk
        (fun s -> if s = symbol then term else mk_const srk s)
    in
    Symbol.Map.add symbol term (Symbol.Map.map subst_symbol subst)
  in
  let rec loop () =
    match Smt.Solver.get_model solver with
    | `Sat interp ->
       let implicant =
         match select_implicant srk interp phi with
         | Some x -> specialize_floor_cube srk interp x
         | None -> assert false
       in
       (* Find substitutions for symbols involved in equations, along
          with divisibility constarints *)
       let (subst, div_constraints) =
         let (oriented_eqs, _) =
           List.filter_map (fun atom ->
               match Interpretation.destruct_atom srk atom with
               | `ArithComparison (op, s, t) ->
                  begin match simplify_atom srk op s t with
                  | `CompareZero (`Eq, t) -> Some t
                  | _ -> None
                  end
               | _ -> None)
             implicant
           |> _orient project_int
         in
         List.fold_left (fun (subst, div_constraints) (a, dim, rhs) ->
             let rhs_qq =
               ZZVector.enum rhs
               /@ (fun (b, dim) -> (QQ.of_zz b, dim))
               |> V.of_enum
             in
             let sym = match Linear.sym_of_dim dim with
               | Some s -> s
               | None -> assert false
             in
             let sym_div = mk_divides srk a rhs_qq in
             let rhs_term =
               Linear.of_linterm srk
                 (V.scalar_mul (QQ.of_zzfrac (ZZ.of_int 1) a) rhs_qq)
             in
             (seq_subst sym rhs_term subst, sym_div::div_constraints))
           (Symbol.Map.empty, [])
           oriented_eqs
       in
       let implicant =
         List.map (substitute_map srk subst) (div_constraints@implicant)
       in
       (* Add substitituions for symbols *not* involved in equations
          to subst *)
       let subst =
         Symbol.Set.fold (fun s (subst, implicant) ->
             if Symbol.Map.mem s subst then
               (* Skip symbols involved in equations *)
               (subst, implicant)
             else if typ_symbol srk s = `TyInt then
               let vt = select_int_term srk interp s implicant in

               (* floor(term/div) + offset ~> (term - ([[term]] mod div))/div + offset,
               and add constraint that div | (term - ([[term]] mod div)) *)
               let term_val =
                 let term_qq = evaluate_linterm (Interpretation.real interp) vt.term in
                 match QQ.to_zz term_qq with
                 | None -> assert false
                 | Some zz -> zz
               in
               let remainder =
                 Mpzf.fdiv_r term_val vt.divisor
               in
               let numerator =
                 V.add_term (QQ.of_zz (ZZ.negate remainder)) const_dim vt.term
               in
               let replacement =
                 V.scalar_mul (QQ.inverse (QQ.of_zz vt.divisor)) numerator
                 |> V.add_term (QQ.of_zz vt.offset) const_dim
                 |> of_linterm srk
               in
               let subst' =
                 substitute_const srk
                   (fun p -> if p = s then replacement else mk_const srk p)
               in
               let divides = mk_divides srk vt.divisor numerator in
               let implicant =
                 BatList.filter (not % is_true) (divides::(List.map subst' implicant))
               in
               (seq_subst s (term_of_virtual_term srk vt) subst,
                implicant)
             else if typ_symbol srk s = `TyReal then
               let implicant_s =
                 List.filter (fun atom -> Symbol.Set.mem s (symbols atom)) implicant
               in
               let t = Linear.of_linterm srk (select_real_term srk interp s implicant_s) in
               let subst' =
                 substitute_const srk
                   (fun p -> if p = s then t else mk_const srk p)
               in
               let implicant =
                 BatList.filter (not % is_true) (List.map subst' implicant)
               in
               (seq_subst s t subst,
                implicant)
             else assert false)
           project
           (subst, implicant)
         |> fst
       in
       let disjunct =
         substitute_map
           srk
           subst
           (if dnf then (mk_and srk (div_constraints@implicant))
            else (mk_and srk (phi::div_constraints)))
         |> SrkSimplify.simplify_terms srk
       in
       disjuncts := disjunct::(!disjuncts);
       Smt.Solver.add solver [mk_not srk disjunct];
       loop ()
    | `Unsat -> mk_or srk (!disjuncts)
    | `Unknown -> raise Unknown
  in
  Smt.Solver.add solver [phi];
  loop ()

(* Loos-Weispfenning virtual terms, plus a virtual term CUnknown
   indicating failure of virtual term selection.  Substituting
   CUnknown into an atom replaces it with true, resulting in
   over-approximate quantifier elimination. *)
type 'a cover_virtual_term =
  | CMinusInfinity
  | CPlusEpsilon of 'a arith_term
  | CTerm of 'a arith_term
  | CUnknown

let pp_cover_virtual_term srk formatter =
  function
  | CMinusInfinity -> Format.pp_print_string formatter "-oo"
  | CPlusEpsilon t ->
    Format.fprintf formatter "%a + epsilon" (ArithTerm.pp srk) t
  | CTerm t -> ArithTerm.pp srk formatter t
  | CUnknown -> Format.pp_print_string formatter "??"

let cover_virtual_term srk interp x atoms =
  let merge lower lower' =
    match lower, lower' with
    | None, x | x, None -> x
    | Some (lower, lower_val), Some (lower', lower_val') ->
      if QQ.lt lower_val lower_val' then
        Some (lower', lower_val')
      else
        Some (lower, lower_val)
  in
  let get_equal_term atom =
    match Interpretation.destruct_atom srk atom with
    | `Literal (_, _) -> None
    | `ArrEq _ -> None
    | `ArithComparison (`Lt, _, _) -> None
    | `ArithComparison (_, s, t) ->
      let sval = Interpretation.evaluate_term interp s in
      let tval = Interpretation.evaluate_term interp t in
      if QQ.equal sval tval then
        match SrkSimplify.isolate_linear srk x (mk_sub srk s t) with
        | Some (a, b) when not (QQ.equal a QQ.zero) ->
          let term =
            mk_mul srk [mk_real srk (QQ.inverse (QQ.negate a)); b]
          in
          if typ_symbol srk x = `TyInt && expr_typ srk term = `TyReal then
            Some (mk_floor srk term)
          else
            Some term
        | _ -> None
      else
        None
  in
  let get_vt atom =
    match Interpretation.destruct_atom srk atom with
    | `Literal (_, _) -> None
    | `ArrEq _ -> None
    | `ArithComparison (_, s, t) ->
      match SrkSimplify.isolate_linear srk x (mk_sub srk s t) with
      | None -> raise Nonlinear
      | Some (a, b) when QQ.lt a QQ.zero ->
        let b_over_a = mk_mul srk [mk_real srk (QQ.inverse (QQ.negate a)); b] in
        let b_over_a_val = Interpretation.evaluate_term interp b_over_a in
        Some (b_over_a, b_over_a_val)
      | _ -> None
  in
  try CTerm (BatList.find_map get_equal_term atoms)
  with Not_found ->
    (try
       begin match List.fold_left merge None (List.map get_vt atoms) with
         | Some (lower, _) -> CPlusEpsilon lower
         | None -> CMinusInfinity
       end
     with Nonlinear -> CUnknown)

let cover_virtual_substitution srk x virtual_term phi =
  let zero = mk_real srk QQ.zero in
  let replace_atom op s t =
    assert (ArithTerm.equal zero (mk_real srk QQ.zero));
    match op, SrkSimplify.isolate_linear srk x (mk_sub srk s t), virtual_term with
    | (_, None, _) -> mk_true srk
    | (`Leq, Some (a, _), _) when QQ.equal a QQ.zero ->
      mk_leq srk s t
    | (`Lt, Some (a, _), _) when QQ.equal a QQ.zero ->
      mk_lt srk s t
    | (`Eq, Some (a, _), _) when QQ.equal a QQ.zero ->
      mk_eq srk s t
    | (`Eq, Some (_, _), CPlusEpsilon _)
    | (`Eq, Some (_, _), CMinusInfinity) -> mk_false srk
    | (_, Some (a, _), CMinusInfinity) ->
      if QQ.lt a QQ.zero then mk_false srk
      else mk_true srk
    | (_, Some (a, b), CPlusEpsilon t) ->
        (* a(t+epsilon) + b <= 0 *)
      if QQ.lt a QQ.zero then
        mk_leq srk (mk_add srk [mk_mul srk [mk_real srk a; t]; b]) zero
      else
        mk_lt srk (mk_add srk [mk_mul srk [mk_real srk a; t]; b]) zero
    | (_, _, _) -> assert false
  in
  match virtual_term with
  | CTerm term ->
    let subst s =
      if s = x then term else mk_const srk s
    in
    substitute_const srk subst phi
  | CUnknown ->
    let drop expr =
      match destruct srk expr with
      | `Atom _ ->
        if Symbol.Set.mem x (symbols expr) then
          (mk_true srk :> ('a, typ_fo) expr)
        else
          expr
      | _ -> expr
    in
    rewrite srk ~up:drop phi
  | _ ->
    map_arith_atoms srk replace_atom phi

let mbp_cover ?(dnf=true) srk exists phi =
  let phi = eliminate_ite srk phi in
  let phi = rewrite srk ~down:(nnf_rewriter srk) phi in
  let project =
    Symbol.Set.filter (not % exists) (symbols phi)
  in
  let phi = eliminate_ite srk phi in
  let solver = Smt.mk_solver srk in
  let disjuncts = ref [] in
  let rec loop () =
    match Smt.Solver.get_model solver with
    | `Sat m ->
      let implicant =
        match select_implicant srk m phi with
        | Some x -> x
        | None -> assert false
      in
      let (_, psi) =
        Symbol.Set.fold (fun s (implicant, disjunct) ->
            let vt = cover_virtual_term srk m s implicant in
            logf "Found %a -> %a" (pp_symbol srk) s (pp_cover_virtual_term srk) vt;
            let implicant' =
              List.map (cover_virtual_substitution srk s vt) implicant
            in
            logf "Implicant' %a" (Formula.pp srk) (mk_and srk implicant');
            (implicant', cover_virtual_substitution srk s vt disjunct))
          project
          (implicant, if dnf then (mk_and srk implicant) else phi)
      in

      disjuncts := psi::(!disjuncts);
      Smt.Solver.add solver [mk_not srk psi];
      loop ()
    | `Unsat -> mk_or srk (!disjuncts)
    | `Unknown -> raise Unknown
  in
  Smt.Solver.add solver [phi];
  loop ()

let local_project_cube srk exists model cube =
  (* Set of symbols to be projected *)
  let project =
    List.fold_left
      (fun set phi -> Symbol.Set.union set (Symbol.Set.filter (not % exists) (symbols phi)))
      Symbol.Set.empty
      cube
  in
  let is_true phi =
    match Formula.destruct srk phi with
    | `Tru -> true
    | _ -> false
  in

  Symbol.Set.fold (fun symbol cube ->
      let vt = cover_virtual_term srk model symbol cube in
      List.map (cover_virtual_substitution srk symbol vt) cube
      |> List.filter (not % is_true))
    project
    cube
