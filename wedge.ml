open Syntax
open Apak
open BatPervasives

module V = Linear.QQVector
module Monomial = Polynomial.Monomial
module P = Polynomial.Mvp
module Scalar = Apron.Scalar
module Coeff = Apron.Coeff
module Abstract0 = Apron.Abstract0
module Linexpr0 = Apron.Linexpr0
module Lincons0 = Apron.Lincons0
module Dim = Apron.Dim

include Log.Make(struct let name = "ark.wedge" end)

module Int = struct
  type t = int [@@deriving show,ord]
  let tag k = k
end

let qq_of_scalar = function
  | Scalar.Float k -> QQ.of_float k
  | Scalar.Mpqf k  -> k
  | Scalar.Mpfrf k -> Mpfrf.to_mpqf k

let qq_of_coeff = function
  | Coeff.Scalar s -> Some (qq_of_scalar s)
  | Coeff.Interval _ -> None

let qq_of_coeff_exn = function
  | Coeff.Scalar s -> qq_of_scalar s
  | Coeff.Interval _ -> invalid_arg "qq_of_coeff_exn: argument must be a scalar"

let coeff_of_qq = Coeff.s_of_mpqf

let scalar_zero = Coeff.s_of_int 0
let scalar_one = Coeff.s_of_int 1

module IntMap = Apak.Tagged.PTMap(Int)
module IntSet = Apak.Tagged.PTSet(Int)

(* An sd_term is a term with synthetic dimensions, which can itself be used to
   define a synthetic dimension.  And sd_term should be interpreted within the
   context of an environment that maps positive integers to (synthetic)
   dimensions: the vectors that appear in an sd_term represent affine terms
   over these dimensions, with the special dimension (-1) corresponding to the
   number 1.  *)
type sd_term = Mul of V.t * V.t
             | Inv of V.t
             | Mod of V.t * V.t
             | Floor of V.t
             | App of symbol * (V.t list)


let ensure_nonlinear_symbols ark =
  List.iter
    (fun (name, typ) ->
       if not (is_registered_name ark name) then
         register_named_symbol ark name typ)
    [("pow", (`TyFun ([`TyReal; `TyReal], `TyReal)));
     ("log", (`TyFun ([`TyReal; `TyReal], `TyReal)))]

(* Env needs to map a set of synthetic terms into an initial segment of the
   naturals, with all of the integer-typed synthetic terms mapped to smaller
   naturals than real-typed synthetic terms *)
module Env = struct
  module A = BatDynArray

  type 'a t =
    { ark : 'a context;
      term_id : (sd_term, int) Hashtbl.t;
      id_def : (sd_term * int * [`TyInt | `TyReal]) A.t;
      int_dim : int A.t;
      real_dim : int A.t }

  let const_id = -1

  let int_dim env = A.length env.int_dim

  let real_dim env = A.length env.real_dim

  let dim env = int_dim env + real_dim env

  let mk_empty ark =
    { ark = ark;
      term_id = Hashtbl.create 991;
      id_def = A.create ();
      int_dim = A.create ();
      real_dim = A.create () }

  let copy env =
    { ark = env.ark;
      term_id = Hashtbl.copy env.term_id;
      id_def = A.copy env.id_def;
      int_dim = A.copy env.int_dim;
      real_dim = A.copy env.real_dim }

  let sd_term_of_id env id =
    let (term, _, _) = A.get env.id_def id in
    term

  let rec term_of_id env id =
    match sd_term_of_id env id with
    | Mul (x, y) -> mk_mul env.ark [term_of_vec env x; term_of_vec env y]
    | Inv x -> mk_div env.ark (mk_real env.ark QQ.one) (term_of_vec env x)
    | Mod (x, y) -> mk_mod env.ark (term_of_vec env x) (term_of_vec env y)
    | Floor x -> mk_floor env.ark (term_of_vec env x)
    | App (func, args) -> mk_app env.ark func (List.map (term_of_vec env) args)

  and term_of_vec env vec =
    (V.enum vec)
    /@ (fun (coeff, id) ->
        if id = const_id then
          mk_real env.ark coeff
        else if QQ.equal QQ.one coeff then
          term_of_id env id
        else
          mk_mul env.ark [mk_real env.ark coeff; term_of_id env id])
    |> BatList.of_enum
    |> mk_add env.ark

  let level_of_id env id =
    let (_, level, _) = A.get env.id_def id in
    level

  let type_of_id env id =
    let (_, _, typ) = A.get env.id_def id in
    typ

  let dim_of_id env id =
    let intd = A.length env.int_dim in
    match type_of_id env id with
    | `TyInt -> ArkUtil.search id env.int_dim
    | `TyReal -> intd + (ArkUtil.search id env.real_dim)

  let id_of_dim env dim =
    let intd = A.length env.int_dim in
    try
      if dim >= intd then
        A.get env.real_dim (dim - intd)
      else
        A.get env.int_dim dim
    with BatDynArray.Invalid_arg _ ->
      invalid_arg "Env.id_of_dim: out of bounds"

  let level_of_vec env vec =
    BatEnum.fold
      (fun level (_, id) ->
         if id = const_id then
           level
         else
           max level (level_of_id env id))
      (-1)
      (V.enum vec)

  let type_of_vec env vec =
    let is_integral (coeff, id) =
      QQ.to_zz coeff != None
      && (id = const_id || type_of_id env id = `TyInt)
    in
    if BatEnum.for_all is_integral (V.enum vec) then
      `TyInt
    else
      `TyReal

  let join_typ s t = match s,t with
    | `TyInt, `TyInt -> `TyInt
    | _, _ -> `TyReal

  let ark env = env.ark

  let pp formatter env =
    Format.fprintf formatter "[@[<v 0>";
    env.id_def |> A.iteri (fun id _ ->
        Format.fprintf formatter "%d -> %a (%d, %s)@;"
          id
          (Term.pp env.ark) (term_of_id env id)
          (dim_of_id env id)
          (match type_of_id env id with | `TyInt -> "int" | `TyReal -> "real"));
    Format.fprintf formatter "@]]"

  let rec pp_vector env formatter vec =
    let pp_elt formatter (k, id) =
      if id = const_id then
        QQ.pp formatter k
      else if QQ.equal k QQ.one then
        pp_sd_term env formatter (sd_term_of_id env id)
      else
        Format.fprintf formatter "%a@ * (@[%a@])"
          QQ.pp k
          (pp_sd_term env) (sd_term_of_id env id)
    in
    let pp_sep formatter () = Format.fprintf formatter " +@ " in
    if V.is_zero vec then
      Format.pp_print_string formatter "0"
    else
      Format.fprintf formatter "@[<hov 1>%a@]"
        (ApakEnum.pp_print_enum ~pp_sep pp_elt) (V.enum vec)

  and pp_sd_term env formatter = function
    | Mul (x, y) ->
      Format.fprintf formatter "@[<hov 1>(%a)@ * (%a)@]"
        (pp_vector env) x
        (pp_vector env) y
    | Inv x ->
      Format.fprintf formatter "1/(@[<hov 1>%a@])"
        (pp_vector env) x
    | Mod (x, y) ->
      Format.fprintf formatter "@[<hov 1>(%a)@ mod (%a)@]"
        (pp_vector env) x
        (pp_vector env) y
    | Floor x ->
      Format.fprintf formatter "floor(@[%a@])"
        (pp_vector env) x
    | App (const, []) ->
      Format.fprintf formatter "%a" (pp_symbol env.ark) const
    | App (func, args) ->
      let pp_comma formatter () = Format.fprintf formatter ",@ " in
      Format.fprintf formatter "%a(@[<hov 1>%a@])"
        (pp_symbol env.ark) func
        (ApakEnum.pp_print_enum ~pp_sep:pp_comma (pp_vector env))
        (BatList.enum args)

  let get_term_id ?(register=true) env t =
    if Hashtbl.mem env.term_id t then
      Hashtbl.find env.term_id t
    else if register then
      let id = A.length env.id_def in
      let (typ, level) = match t with
        | Mul (s, t) | Mod (s, t) ->
          (join_typ (type_of_vec env s) (type_of_vec env t),
           max (level_of_vec env s) (level_of_vec env t))
        | Floor x ->
          (`TyInt, level_of_vec env x)
        | Inv x ->
          (`TyReal, level_of_vec env x)
        | App (func, args) ->
          let typ =
            match typ_symbol env.ark func with
            | `TyFun (_, `TyInt) | `TyInt -> `TyInt
            | `TyFun (_, `TyReal) | `TyReal -> `TyReal
            | `TyFun (_, `TyBool) | `TyBool -> `TyInt
          in
          let level =
            List.fold_left max 0 (List.map (level_of_vec env) args)
          in
          (typ, level)
      in
      A.add env.id_def (t, level, typ);
      Hashtbl.add env.term_id t id;
      begin match typ with
        | `TyInt -> A.add env.int_dim id
        | `TyReal -> A.add env.real_dim id
      end;
      logf ~level:`trace "Registered %s: %d -> %a"
        (match typ with `TyInt -> "int" | `TyReal -> "real")
        id
        (pp_sd_term env) t;
      id
    else
      raise Not_found

  let const_of_vec vec =
    let (const_coeff, rest) = V.pivot const_id vec in
    if V.is_zero rest then
      Some const_coeff
    else
      None

  let vec_of_term ?(register=true) env =
    let rec alg = function
      | `Real k -> V.of_term k const_id
      | `App (symbol, []) ->
        V.of_term QQ.one (get_term_id ~register env (App (symbol, [])))

      | `App (symbol, xs) ->
        let xs =
          List.map (fun x ->
              match refine env.ark x with
              | `Term t -> Term.eval env.ark alg t
              | `Formula _ -> assert false (* TODO *))
            xs
        in
        V.of_term QQ.one (get_term_id ~register env (App (symbol, xs)))

      | `Var (_, _) -> assert false (* to do *)
      | `Add xs -> List.fold_left V.add V.zero xs
      | `Mul xs ->
        (* Factor out scalar multiplication *)
        let (k, xs) =
          List.fold_right (fun y (k,xs) ->
              match const_of_vec y with
              | Some k' -> (QQ.mul k k', xs)
              | None -> (k, y::xs))
            xs
            (QQ.one, [])
        in
        begin match xs with
          | [] -> V.of_term k const_id
          | x::xs ->
            let mul x y =
              V.of_term QQ.one (get_term_id ~register env (Mul (x, y)))
            in
            V.scalar_mul k (List.fold_left mul x xs)
        end
      | `Binop (`Div, x, y) ->
        let denomenator = V.of_term QQ.one (get_term_id ~register env (Inv y)) in
        let (k, xrest) = V.pivot const_id x in
        if V.equal xrest V.zero then
          V.scalar_mul k denomenator
        else
          V.of_term QQ.one (get_term_id ~register env (Mul (x, denomenator)))
      | `Binop (`Mod, x, y) ->
        V.of_term QQ.one (get_term_id ~register env (Mod (x, y)))
      | `Unop (`Floor, x) ->
        V.of_term QQ.one (get_term_id ~register env (Floor x))
      | `Unop (`Neg, x) -> V.negate x
      | `Ite (_, _, _) -> assert false (* No ites in implicants *)
    in
    Term.eval env.ark alg

  let mem_term env t =
    try
      ignore (vec_of_term ~register:false env t);
      true
    with Not_found -> false

  let vec_of_linexpr env linexpr =
    let vec = ref V.zero in
    Linexpr0.iter (fun coeff dim ->
        match qq_of_coeff coeff with
        | Some qq when QQ.equal QQ.zero qq -> ()
        | Some qq ->
          vec := V.add_term qq (id_of_dim env dim) (!vec)
        | None -> assert false)
      linexpr;
    match qq_of_coeff (Linexpr0.get_cst linexpr) with
    | Some qq -> V.add_term qq const_id (!vec)
    | None -> assert false

  let linexpr_of_vec env vec =
    let mk (coeff, id) = (coeff_of_qq coeff, dim_of_id env id) in
    let (const_coeff, rest) = V.pivot const_id vec in
    Linexpr0.of_list None
      (BatList.of_enum (BatEnum.map mk (V.enum rest)))
      (Some (coeff_of_qq const_coeff))

  (** Convert a vector / id to a polynomial *without multiplicative
      coordinates*.  Multiplicative coordinates are expanded into
      higher-degree polynomials over non-multiplicative coordinates. *)
  let rec hi_poly_of_id env id =
     match sd_term_of_id env id with
     | Mul (x, y) -> P.mul (hi_poly_of_vec env x) (hi_poly_of_vec env y)
     | _ -> P.of_dim id
  and hi_poly_of_vec env vec =
     let (const_coeff, vec) = V.pivot const_id vec in
     V.enum vec
     /@ (fun (coeff, id) -> P.scalar_mul coeff (hi_poly_of_id env id))
    |> BatEnum.fold P.add (P.scalar const_coeff)

  let term_of_polynomial env p =
    (P.enum p)
    /@ (fun (coeff, monomial) ->
        let product =
          BatEnum.fold
            (fun product (id, power) ->
               let term = term_of_id env id in
               BatEnum.fold
                 (fun product _ -> term::product)
                 product
                 (1 -- power))
            [mk_real env.ark coeff]
            (Monomial.enum monomial)
        in
        mk_mul env.ark product)
    |> BatList.of_enum
    |> mk_add env.ark

  let atom_of_lincons env lincons =
    let open Lincons0 in
    let term =
      term_of_vec env (vec_of_linexpr env lincons.linexpr0)
    in
    let zero = mk_real env.ark QQ.zero in
    match lincons.typ with
    | EQ -> mk_eq env.ark term zero
    | SUPEQ -> mk_leq env.ark zero term
    | SUP -> mk_lt env.ark zero term
    | DISEQ | EQMOD _ -> assert false
end

let pp_vector = Env.pp_vector
let pp_sd_term = Env.pp_sd_term

let vec_of_poly = P.vec_of ~const:Env.const_id
let poly_of_vec = P.of_vec ~const:Env.const_id

let get_manager =
  let manager = ref None in
  fun () ->
    match !manager with
    | Some man -> man
    | None ->
      let man = Polka.manager_alloc_strict () in
      manager := Some man;
      man

type 'a t =
  { env : 'a Env.t;
    mutable abstract : (Polka.strict Polka.t) Abstract0.t;
    (* int_dim and real_dim keep track of the number of dimensions in the
       abstract value associated with a wedge, which can get out of sync with the
       number of dimensions known to the environment (by registering new terms).
       update_env gets them back into sync *)
    mutable int_dim : int;
    mutable real_dim : int; }

let pp formatter wedge =
  Abstract0.print
    (fun dim ->
       Apak.Putil.mk_show
         (pp_sd_term wedge.env)
         (Env.sd_term_of_id wedge.env (Env.id_of_dim wedge.env dim)))
    formatter
    wedge.abstract

let show wedge = Apak.Putil.mk_show pp wedge

let env_consistent wedge =
  Env.int_dim wedge.env = wedge.int_dim
  && Env.real_dim wedge.env = wedge.real_dim

(* Should be called when new terms are registered in the environment attached
   to a wedge *)
let update_env wedge =
  let int_dim = Env.int_dim wedge.env in
  let real_dim = Env.real_dim wedge.env in
  let added_int = max 0 (int_dim - wedge.int_dim) in
  let added_real = max 0 (real_dim - wedge.real_dim) in
  let added =
    BatEnum.append
      ((1 -- added_int) /@ (fun _ -> wedge.int_dim))
      ((1 -- added_real) /@ (fun _ -> wedge.int_dim + wedge.real_dim))
    |> BatArray.of_enum
  in
  if added_int + added_real > 0 then begin
    logf ~level:`trace "update env: adding %d integer and %d real dimension(s)"
      added_int
      added_real;
    let abstract =
      Abstract0.add_dimensions
        (get_manager ())
        wedge.abstract
        { Dim.dim = added;
          Dim.intdim = added_int;
          Dim.realdim = added_real }
        false
    in
    wedge.abstract <- abstract;
    wedge.int_dim <- int_dim;
    wedge.real_dim <- real_dim
  end

let top context =
  { env = Env.mk_empty context;
    abstract = Abstract0.top (get_manager ()) 0 0;
    int_dim = 0;
    real_dim = 0 }

let is_top wedge = Abstract0.is_top (get_manager ()) wedge.abstract

let bottom context =
  { env = Env.mk_empty context;
    abstract = Abstract0.bottom (get_manager ()) 0 0;
    int_dim = 0;
    real_dim = 0 }

let is_bottom wedge = Abstract0.is_bottom (get_manager ()) wedge.abstract

let to_atoms wedge =
  BatArray.enum (Abstract0.to_lincons_array (get_manager ()) wedge.abstract)
  /@ (Env.atom_of_lincons wedge.env)
  |> BatList.of_enum

let to_formula wedge =
  let ark = Env.ark wedge.env in
  mk_and ark (to_atoms wedge)

let lincons_of_atom env atom =
  let ark = Env.ark env in
  match Interpretation.destruct_atom ark atom with
  | `Comparison (`Lt, x, y) ->
    Lincons0.make
      (Env.linexpr_of_vec
         env
         (V.add (Env.vec_of_term env y) (V.negate (Env.vec_of_term env x))))
      Lincons0.SUP
  | `Comparison (`Leq, x, y) ->
    Lincons0.make
      (Env.linexpr_of_vec
         env
         (V.add (Env.vec_of_term env y) (V.negate (Env.vec_of_term env x))))
      Lincons0.SUPEQ
  | `Comparison (`Eq, x, y) ->
    Lincons0.make
      (Env.linexpr_of_vec
         env
         (V.add (Env.vec_of_term env y) (V.negate (Env.vec_of_term env x))))
      Lincons0.EQ
  | `Literal (_, _) -> assert false

let bound_vec wedge vec =
  Abstract0.bound_linexpr
    (get_manager ())
    wedge.abstract
    (Env.linexpr_of_vec wedge.env vec)
  |> Interval.of_apron

(* Test whether wedge |= x = y *)
let sat_vec_equation wedge x y =
  let eq_constraint =
    Lincons0.make
      (Env.linexpr_of_vec wedge.env (V.add x (V.negate y)))
      Lincons0.EQ
  in
  Abstract0.sat_lincons (get_manager ()) wedge.abstract eq_constraint

let apron_farkas abstract =
  let open Lincons0 in
  let constraints =
    Abstract0.to_lincons_array (get_manager ()) abstract
  in
  let lambda_constraints =
    (0 -- (Array.length constraints - 1)) |> BatEnum.filter_map (fun dim ->
        match constraints.(dim).typ with
        | SUP | SUPEQ ->
          let lincons =
            Lincons0.make
              (Linexpr0.of_list None [(coeff_of_qq QQ.one, dim)] None)
              SUPEQ
          in
          Some lincons
        | EQ -> None
        | DISEQ | EQMOD _ -> assert false)
    |> BatArray.of_enum
  in
  let lambda_abstract =
    Abstract0.of_lincons_array
      (get_manager ())
      0
      (Array.length constraints)
      lambda_constraints
  in
  let nb_columns =
    let dim = Abstract0.dimension (get_manager ()) abstract in
    (* one extra column for the constant *)
    dim.Dim.intd + dim.Dim.reald + 1
  in
  let columns =
    Array.init nb_columns (fun _ -> Linexpr0.make None)
  in
  for row = 0 to Array.length constraints - 1 do
    constraints.(row).linexpr0 |> Linexpr0.iter (fun coeff col ->
        Linexpr0.set_coeff columns.(col) row coeff);
    Linexpr0.set_coeff
      columns.(nb_columns - 1)
      row
      (Linexpr0.get_cst constraints.(row).linexpr0)
  done;
  (lambda_abstract, columns)

let affine_hull wedge =
  let open Lincons0 in
  BatArray.enum (Abstract0.to_lincons_array (get_manager ()) wedge.abstract)
  |> BatEnum.filter_map (fun lcons ->
      match lcons.typ with
      | EQ -> Some (Env.vec_of_linexpr wedge.env lcons.linexpr0)
      | _ -> None)
  |> BatList.of_enum

let polynomial_cone wedge =
  let open Lincons0 in
  BatArray.enum (Abstract0.to_lincons_array (get_manager ()) wedge.abstract)
  |> BatEnum.filter_map (fun lcons ->
      match lcons.typ with
      | SUPEQ | SUP -> Some (poly_of_vec (Env.vec_of_linexpr wedge.env lcons.linexpr0))
      | _ -> None)
  |> BatList.of_enum

let strengthen ?integrity:(integrity=(fun _ -> ())) wedge =
  ensure_nonlinear_symbols (Env.ark wedge.env);
  let env = wedge.env in
  let ark = Env.ark env in
  let zero = mk_real ark QQ.zero in
  let pow = get_named_symbol ark "pow" in
  let log = get_named_symbol ark "log" in
  let mk_log (base : 'a term) (x : 'a term) = mk_app ark log [base; x] in
  let add_bound_unsafe bound =
    let abstract =
      Abstract0.meet_lincons_array
        (get_manager ())
        wedge.abstract
        [| lincons_of_atom env bound |]
    in
    wedge.abstract <- abstract
  in
  let add_bound precondition bound =
    logf ~level:`trace "Integrity: %a => %a"
      (Formula.pp ark) precondition
      (Formula.pp ark) bound;
    integrity (mk_or ark [mk_not ark precondition; bound]);

    ignore (lincons_of_atom env bound);
    update_env wedge;
    add_bound_unsafe bound
  in

  logf "Before strengthen: %a" pp wedge;

  update_env wedge;
  for id = 0 to Env.dim wedge.env - 1 do
    match Env.sd_term_of_id wedge.env id with
    | Mul (x, y) ->
      if not (Interval.elem QQ.zero (bound_vec wedge x)) then
        ignore (Env.get_term_id wedge.env (Inv x));
      if not (Interval.elem QQ.zero (bound_vec wedge y)) then
        ignore (Env.get_term_id wedge.env (Inv y))
    | _ -> ()
  done;
  update_env wedge;
  
  let wedge_affine_hull = affine_hull wedge in
  let affine_hull_formula =
    ref (wedge_affine_hull
         |> List.map (fun vec -> mk_eq ark (Env.term_of_vec wedge.env vec) zero)
         |> mk_and ark)
  in
  (* Rewrite maintains a Grobner basis for the coordinate ideal + the ideal of
     polynomials vanishing on the underlying polyhedron of the wedge *)
  let rewrite =
    let polyhedron_ideal =
      List.map poly_of_vec wedge_affine_hull
    in
    let coordinate_ideal =
      BatEnum.filter_map (fun id ->
          match Env.sd_term_of_id wedge.env id with
          | Mul (x, y) ->
            Some (P.sub
                    (P.of_dim id)
                    (P.mul (poly_of_vec x) (poly_of_vec y)))
          | Inv x ->
            Some (P.sub (P.mul (poly_of_vec x) (P.of_dim id)) (P.scalar QQ.one))
          | _ -> None)
        (0 -- (Env.dim wedge.env - 1))
      |> BatList.of_enum
    in
    ref (polyhedron_ideal@coordinate_ideal
         |> Polynomial.Rewrite.mk_rewrite Monomial.degrevlex
         |> Polynomial.Rewrite.grobner_basis)
  in
  let pp_dim formatter i =
    Term.pp ark formatter (Env.term_of_id wedge.env i)
  in
  logf "Rewrite: @[<v 0>%a@]" (Polynomial.Rewrite.pp pp_dim) (!rewrite);
  let reduce_vec vec =
    Polynomial.Rewrite.reduce (!rewrite) (poly_of_vec vec)
    |> Env.term_of_polynomial wedge.env
  in

  (* pow-log rule *)
  begin
    let vec_sign vec =
      let ivl = bound_vec wedge vec in
      if Interval.is_positive ivl then
        `Positive
      else if Interval.is_negative ivl then
        `Negative
      else
        `Unknown
    in
    let polynomial_sign p =
      match vec_of_poly (Polynomial.Rewrite.reduce (!rewrite) p) with
      | Some v -> vec_sign v
      | None -> `Unknown
    in
    let exponential_dimensions =
      BatEnum.filter_map (fun id ->
          match Env.sd_term_of_id wedge.env id with
          | App (func, [base; exp]) when func = pow && vec_sign base = `Positive ->
            Some (id,
                  Env.term_of_vec wedge.env base,
                  Env.term_of_vec wedge.env exp)
          | _ -> None)
        (0 -- (Env.dim wedge.env - 1))
      |> BatList.of_enum
    in
    let open Lincons0 in
    Abstract0.to_lincons_array (get_manager ()) wedge.abstract
    |> BatArray.iter (fun lcons ->
        let p =
          Env.hi_poly_of_vec
            wedge.env
            (Env.vec_of_linexpr wedge.env lcons.linexpr0)
        in
        exponential_dimensions |> List.iter (fun (id, base, exp) ->
            (* Rewrite p as m*(base^exp) - t *)
            let (m, t) =
              let id_monomial = Monomial.singleton id 1 in
              BatEnum.fold (fun (m, t) (coeff, monomial) ->
                  match Monomial.div monomial id_monomial with
                  | Some m' -> (P.add_term coeff m' m, t)
                  | None -> (m, P.add_term (QQ.negate coeff) monomial t))
                (P.zero, P.zero)
                (P.enum p)
            in
            let m_sign = polynomial_sign m in
            let t_sign = polynomial_sign t in
            if m_sign != `Unknown && m_sign = t_sign then
              let (m, t) =
                if m_sign = `Positive then
                  (m, t)
                else
                  (P.negate m, P.negate t)
              in
              let m_term = Env.term_of_polynomial wedge.env m in
              let t_term = Env.term_of_polynomial wedge.env t in
              let log_m = mk_log base m_term in
              let log_t = mk_log base t_term in
              update_env wedge;
              (* base > 0 /\ m > 0 /\ t > 0 /\ m*(base^exp) - t >= 0 ==>
                 log(base,m) + exp >= log(base,t) *)
              let hypothesis =
                mk_and ark [mk_lt ark zero base;
                            mk_lt ark zero m_term;
                            mk_lt ark zero t_term;
                            Env.atom_of_lincons wedge.env lcons]
              in
              let conclusion =
                match lcons.typ, m_sign with
                | EQ, _ ->
                  mk_eq ark log_t (mk_add ark [exp; log_m])
                | SUP, `Positive | SUPEQ, `Positive ->
                  mk_leq ark log_t (mk_add ark [exp; log_m])
                | SUP, `Negative | SUPEQ, `Negative ->
                  mk_leq ark (mk_add ark [exp; log_m]) log_t
                | _, _ -> assert false
              in
              add_bound hypothesis conclusion))
  end;

  (* Equational saturation.  A polyhedron P is equationally saturated if every
     degree-1 polynomial in the ideal of polynomials vanishing on P + the
     coordinate ideal vanishes on P.  This procedure computes the greatest
     equationally saturated polyhedron contained in the underlying wedge of the
     polyhedron.  *)
  let saturated = ref false in

  (* Hashtable mapping canonical forms of nonlinear terms to their
     representative terms. *)
  let canonical = ExprHT.create 991 in
  while not !saturated do
    saturated := true;
    for id = 0 to Env.dim wedge.env - 1 do
      let term = Env.term_of_id wedge.env id in
      (* TODO: track the equations that were actually used in reductions rather
         than just using the affine hull as the precondition. *)
      let reduced_id =
        match vec_of_poly (Polynomial.Rewrite.reduce (!rewrite) (P.of_dim id)) with
        | Some p -> p
        | None ->
          (* Reducing a linear polynomial must result in another linear
             polynomial *)
          assert false
      in
      let reduced_term = Env.term_of_vec wedge.env reduced_id in
      add_bound (!affine_hull_formula) (mk_eq ark term reduced_term);

      (* congruence closure *)
      let add_canonical reduced =
        (* Add [reduced->term] to the canonical map.  Or if there's already a
           mapping [reduced->rep], add the equation rep=term *)
        if ExprHT.mem canonical reduced then
          (* Don't need an integrity formula (congruence is free), so don't
             call add_bound. *)
          add_bound_unsafe (mk_eq ark term (ExprHT.find canonical reduced))
        else
          ExprHT.add canonical reduced term
      in
      begin match Env.sd_term_of_id wedge.env id with
      | App (_, []) | Mul (_, _) -> ()
      | App (func, args) ->
        add_canonical (mk_app ark func (List.map reduce_vec args))
      | Inv t ->
        add_canonical (mk_div ark (mk_real ark QQ.one) (reduce_vec t))
      | Mod (num, den) ->
        add_canonical (mk_mod ark (reduce_vec num) (reduce_vec den))
      | Floor t ->
        add_canonical (mk_floor ark (reduce_vec t))
      end;
    done;
    (* Check for new polynomials vanishing on the underlying polyhedron *)
    affine_hull wedge |> List.iter (fun vec ->
        let reduced =
          Polynomial.Rewrite.reduce (!rewrite) (poly_of_vec vec)
        in
        if not (P.equal P.zero reduced) then begin
          let reduced_term = Env.term_of_polynomial wedge.env reduced in
          saturated := false;
          rewrite := Polynomial.Rewrite.add_saturate (!rewrite) reduced;
          affine_hull_formula := mk_and ark [!affine_hull_formula;
                                             mk_eq ark reduced_term zero]
        end);
  done;

  (* Compute bounds for synthetic dimensions using the bounds of their
     operands *)
  for id = 0 to Env.dim wedge.env - 1 do
    let term = Env.term_of_id wedge.env id in
    match Env.sd_term_of_id wedge.env id with
    | Mul (x, y) ->
      let go (x,x_ivl,x_term) (y,y_ivl,y_term) =
        if Interval.is_nonnegative y_ivl then
          begin
            let y_nonnegative = mk_leq ark (mk_real ark QQ.zero) y_term in
            (match Interval.lower x_ivl with
             | Some lo ->
               add_bound
                 (mk_and ark [y_nonnegative; mk_leq ark (mk_real ark lo) x_term])
                 (mk_leq ark (Env.term_of_vec env (V.scalar_mul lo y)) term)
             | None -> ());
            (match Interval.upper x_ivl with
             | Some hi ->
               add_bound
                 (mk_and ark [y_nonnegative; mk_leq ark x_term (mk_real ark hi)])
                 (mk_leq ark term (Env.term_of_vec env (V.scalar_mul hi y)))

             | None -> ())
          end
        else if Interval.is_nonpositive y_ivl then
          begin
            let y_nonpositive = mk_leq ark y_term (mk_real ark QQ.zero) in
            (match Interval.lower x_ivl with
             | Some lo ->
               add_bound
                 (mk_and ark [y_nonpositive; mk_leq ark (mk_real ark lo) x_term])
                 (mk_leq ark term (Env.term_of_vec env (V.scalar_mul lo y)));
             | None -> ());
            (match Interval.upper x_ivl with
             | Some hi ->
               add_bound
                 (mk_and ark [y_nonpositive; mk_leq ark x_term (mk_real ark hi)])
                 (mk_leq ark (Env.term_of_vec env (V.scalar_mul hi y)) term);
             | None -> ())
          end
        else
          ()
      in

      let x_ivl = bound_vec wedge x in
      let y_ivl = bound_vec wedge y in
      let x_term = Env.term_of_vec env x in
      let y_term = Env.term_of_vec env y in

      go (x,x_ivl,x_term) (y,y_ivl,y_term);
      go (y,y_ivl,y_term) (x,x_ivl,x_term);

      let mul_ivl = Interval.mul x_ivl y_ivl in
      let mk_ivl x interval =
        let lower =
          match Interval.lower interval with
          | Some lo -> mk_leq ark (mk_real ark lo) x
          | None -> mk_true ark
        in
        let upper =
          match Interval.upper interval with
          | Some hi -> mk_leq ark x (mk_real ark hi)
          | None -> mk_true ark
        in
        mk_and ark [lower; upper]
      in
      let precondition =
        mk_and ark [mk_ivl x_term x_ivl; mk_ivl y_term y_ivl]
      in
      (match Interval.lower mul_ivl with
       | Some lo -> add_bound precondition (mk_leq ark (mk_real ark lo) term)
       | None -> ());
      (match Interval.upper mul_ivl with
       | Some hi -> add_bound precondition (mk_leq ark term (mk_real ark hi))
       | None -> ())

    | Floor x ->
      let x_term = Env.term_of_vec env x in
      let _true = mk_true ark in
      add_bound _true (mk_leq ark term x_term);
      add_bound _true (mk_lt ark
                         (mk_add ark [x_term; mk_real ark (QQ.of_int (-1))])
                         term)

    | Inv x ->
      (* TODO: preconditions can be weakened *)
      let x_ivl = bound_vec wedge x in
      let x_term = Env.term_of_vec env x in
      let precondition =
        let lower =
          match Interval.lower x_ivl with
          | Some lo -> [mk_leq ark (mk_real ark lo) x_term]
          | None -> []
        in
        let upper =
          match Interval.upper x_ivl with
          | Some hi -> [mk_leq ark x_term (mk_real ark hi)]
          | None -> []
        in
        mk_and ark (lower@upper)
      in
      let inv_ivl = Interval.div (Interval.const QQ.one) x_ivl in
      begin match Interval.lower inv_ivl with
        | Some lo -> add_bound precondition (mk_leq ark (mk_real ark lo) term)
        | _ -> ()
      end;
      begin match Interval.upper inv_ivl with
        | Some hi -> add_bound precondition (mk_leq ark term (mk_real ark hi))
        | _ -> ()
      end

    | App (func, [base; exp]) when func = log ->
      let base_ivl = bound_vec wedge base in
      let exp_ivl = bound_vec wedge exp in

      let mk_interval t ivl =
        let lo = match Interval.lower ivl with
          | Some lo -> mk_leq ark (mk_real ark lo) t
          | None -> mk_true ark
        in
        let hi = match Interval.upper ivl with
          | Some hi -> mk_leq ark t (mk_real ark hi)
          | None -> mk_true ark
        in
        (lo, hi)
      in
      let precondition =
        let (lo,hi) = mk_interval (Env.term_of_vec env base) base_ivl in
        let (lo',hi') = mk_interval (Env.term_of_vec env exp) exp_ivl in
        mk_and ark [lo;hi;lo';hi']
      in
      let (lo,hi) = mk_interval term (Interval.log base_ivl exp_ivl) in
      add_bound precondition lo;
      add_bound precondition hi

    | Mod (x, y) ->
      let y_ivl = bound_vec wedge y in
      let zero = mk_real ark QQ.zero in
      add_bound (mk_true ark) (mk_leq ark zero term);
      if Interval.is_positive y_ivl then
        let y_term = Env.term_of_vec env y in
        add_bound (mk_lt ark zero y_term) (mk_lt ark term y_term)
      else if Interval.is_negative y_ivl then
        let y_term = Env.term_of_vec env y in
        add_bound (mk_lt ark y_term zero) (mk_lt ark term (mk_neg ark y_term))
      else
        ()

    | App (func, args) -> ()
  done;

  let mk_geqz p = (* p >= 0 *)
    mk_leq ark (mk_neg ark (Env.term_of_polynomial wedge.env p)) zero
  in
  let rec add_products = function
    | [] -> ()
    | (p::cone) ->
      cone |> List.iter (fun q ->
          match vec_of_poly (Polynomial.Rewrite.reduce (!rewrite) (P.mul p q)) with
          | Some r ->
            let precondition =
              mk_and ark [!affine_hull_formula;
                          mk_geqz p;
                          mk_geqz q]
            in
            let r_geqz = (* r >= 0 *)
              mk_leq ark (Env.term_of_vec wedge.env (V.negate r)) zero
            in
            add_bound precondition r_geqz
          | None -> ());
      add_products cone
  in
  add_products (polynomial_cone wedge);

  (* Tighten integral dimensions *)
  for id = 0 to Env.dim wedge.env - 1 do
    match Env.type_of_id wedge.env id with
    | `TyInt ->
      let term = Env.term_of_id wedge.env id in
      let interval = bound_vec wedge (V.of_term QQ.one id) in
      begin
        match Interval.lower interval with
        | Some lo -> add_bound_unsafe (mk_leq ark (mk_real ark lo) term)
        | None -> ()
      end;
      begin
        match Interval.upper interval with
        | Some hi -> add_bound_unsafe (mk_leq ark term (mk_real ark hi))
        | None -> ()
      end
    | _ -> ()
  done;
  logf "After strengthen: %a" pp wedge;
  wedge

let of_atoms ark ?integrity:(integrity=(fun _ -> ())) atoms =
  let env = Env.mk_empty ark in
  let register_terms atom =
    match Interpretation.destruct_atom ark atom with
    | `Comparison (_, x, y) ->
      ignore (Env.vec_of_term env x);
      ignore (Env.vec_of_term env y)
    | `Literal (_, _) -> assert false
  in
  List.iter register_terms atoms;
  let int_dim = Env.int_dim env in
  let real_dim = Env.real_dim env in
  let abstract =
    Abstract0.of_lincons_array
      (get_manager ())
      int_dim
      real_dim
      (Array.of_list (List.map (lincons_of_atom env) atoms))
  in
  strengthen ~integrity { env; abstract; int_dim; real_dim }

let of_atoms ark ?integrity:(integrity=(fun _ -> ())) atoms =
  Log.time "wedge.of_atom" (of_atoms ark ~integrity) atoms

let common_env wedge wedge' =
  let ark = Env.ark wedge.env in
  let env = Env.mk_empty ark in
  let register_terms atom =
    match Interpretation.destruct_atom ark atom with
    | `Comparison (_, x, y) ->
      ignore (Env.vec_of_term env x);
      ignore (Env.vec_of_term env y);
    | `Literal (_, _) -> assert false
  in
  let atoms = to_atoms wedge in
  let atoms' = to_atoms wedge' in
  List.iter register_terms atoms;
  List.iter register_terms atoms';
  let int_dim = Env.int_dim env in
  let real_dim = Env.real_dim env in
  let abstract =
    Abstract0.of_lincons_array
      (get_manager ())
      int_dim
      real_dim
      (Array.of_list (List.map (lincons_of_atom env) atoms))
  in
  let abstract' =
    Abstract0.of_lincons_array
      (get_manager ())
      int_dim
      real_dim
      (Array.of_list (List.map (lincons_of_atom env) atoms'))
  in
  ({ env = env; abstract = abstract; int_dim; real_dim },
   { env = env; abstract = abstract'; int_dim; real_dim })

let join ?integrity:(integrity=(fun _ -> ())) wedge wedge' =
  if is_bottom wedge then wedge'
  else if is_bottom wedge' then wedge
  else
    let (wedge, wedge') = common_env wedge wedge' in
    let wedge = strengthen ~integrity wedge in
    let wedge' = strengthen ~integrity wedge' in
    update_env wedge; (* strengthening wedge' may add dimensions to the
                            common environment -- add those dimensions to
                            wedge *)
    { env = wedge.env;
      int_dim = wedge.int_dim;
      real_dim = wedge.real_dim;
      abstract =
        Abstract0.join (get_manager ()) wedge.abstract wedge'.abstract }

let equal wedge wedge' =
  let ark = Env.ark wedge.env in
  let phi = Nonlinear.uninterpret ark (to_formula wedge) in
  let phi' = Nonlinear.uninterpret ark (to_formula wedge') in
  match Smt.is_sat ark (mk_not ark (mk_iff ark phi phi')) with
  | `Sat -> false
  | `Unsat -> true
  | `Unknown -> assert false

(* Remove dimensions from an abstract value so that it has the specified
   number of integer and real dimensions *)
let apron_set_dimensions new_int new_real abstract =
  let open Dim in
  let abstract_dim = Abstract0.dimension (get_manager ()) abstract in
  let remove_int = abstract_dim.intd - new_int in
  let remove_real = abstract_dim.reald - new_real in
  if remove_int > 0 || remove_real > 0 then
    let remove =
      BatEnum.append
        (new_int -- (abstract_dim.intd - 1))
        ((abstract_dim.intd + new_real)
         -- (abstract_dim.intd + abstract_dim.reald - 1))
      |> BatArray.of_enum
    in
    logf ~level:`trace "Remove %d int, %d real: %a" remove_int remove_real
      (ApakEnum.pp_print_enum Format.pp_print_int) (BatArray.enum remove);
    assert (remove_int + remove_real = (Array.length remove));
    Abstract0.remove_dimensions
      (get_manager ())
      abstract
      { dim = remove;
        intdim = remove_int;
        realdim = remove_real }
  else
    abstract

(** Project a set of coordinates out of an abstract value *)
let forget_ids env abstract forget =
  let forget_dims =
    Array.of_list (List.map (Env.dim_of_id env) forget)
  in
  BatArray.sort Pervasives.compare forget_dims;
  Abstract0.forget_array
    (get_manager ())
    abstract
    forget_dims
    false

(* Get a list of symbolic lower and upper bounds for a vector, expressed in
   terms of identifiers that do not belong to forget *)
let symbolic_bounds_vec wedge vec forget =
  assert (env_consistent wedge);

  (* Add one real dimension to store the vector *)
  let vec_dim = wedge.int_dim + wedge.real_dim in
  let abstract =
    Abstract0.add_dimensions
      (get_manager ())
      wedge.abstract
      { Dim.dim = [| vec_dim |];
        Dim.intdim = 0;
        Dim.realdim = 1 }
      false
  in
  (* Store the vector in vec_dim *)
  begin
    let linexpr = Env.linexpr_of_vec wedge.env vec in
    Linexpr0.set_coeff linexpr vec_dim (Coeff.s_of_int (-1));
    Abstract0.meet_lincons_array_with
      (get_manager ())
      abstract
      [| Lincons0.make linexpr Lincons0.SUPEQ |]
  end;
  (* Project undesired identifiers *)
  let abstract = forget_ids wedge.env abstract forget in

  (* Compute bounds *)
  let lower = ref [] in
  let upper = ref [] in
  Abstract0.to_lincons_array (get_manager ()) abstract
  |> BatArray.iter (fun lincons ->
      let open Lincons0 in
      let a =
        qq_of_coeff_exn (Linexpr0.get_coeff lincons.linexpr0 vec_dim)
      in
      if not (QQ.equal a QQ.zero) then begin
        (* Write lincons.linexpr0 as "vec comp bound" *)
        Linexpr0.set_coeff lincons.linexpr0 vec_dim (coeff_of_qq QQ.zero);
        let bound =
          Env.vec_of_linexpr wedge.env lincons.linexpr0
          |> V.scalar_mul (QQ.negate (QQ.inverse a))
          |> Env.term_of_vec wedge.env
        in
        match lincons.typ with
        | SUP | SUPEQ ->
          if QQ.lt QQ.zero a then
            lower := bound::(!lower)
          else
            upper := bound::(!upper)
        | EQ ->
          lower := bound::(!lower);
          upper := bound::(!upper)
        | _ -> ()
      end);
  (!lower, !upper)

let exists
    ?integrity:(integrity=(fun _ -> ()))
    ?subterm:(subterm=(fun _ -> true))
    p
    wedge =

  let ark = Env.ark wedge.env in
  let env = wedge.env in

  (* Orient equalities as rewrite rules to eliminate variables that should be
     projected out of the formula *)
  let rewrite_map =
    let keep id =
      id = Env.const_id || match Env.sd_term_of_id wedge.env id with
      | App (symbol, []) -> p symbol && subterm symbol
      | _ -> false (* to do: should allow terms containing only non-projected
                      symbols that are allowed as subterms *)
    in
    List.fold_left
      (fun map (id, rhs) ->
         match Env.sd_term_of_id env id with
         | App (symbol, []) ->
           let rhs_term = Env.term_of_vec env rhs in
           logf ~level:`trace "Found rewrite: %a --> %a"
             (pp_symbol ark) symbol
             (Term.pp ark) rhs_term;
           Symbol.Map.add symbol rhs_term map
         | _ -> map)
      Symbol.Map.empty
      (Linear.orient keep (affine_hull wedge))
  in
  let rewrite =
    substitute_const
      ark
      (fun symbol ->
         try Symbol.Map.find symbol rewrite_map
         with Not_found -> mk_const ark symbol)
  in
  let safe_symbol x =
    match typ_symbol ark x with
    | `TyReal | `TyInt | `TyBool -> p x && subterm x
    | `TyFun (_, _) -> true (* don't project function symbols -- particularly
                               not log/pow *)
  in

  let symbol_of id =
    match Env.sd_term_of_id env id with
    | App (symbol, []) -> Some symbol
    | _ -> None
  in

  (* Coordinates that must be projected out *)
  let forget =
    BatEnum.filter (fun id ->
        match symbol_of id with
        | Some symbol -> not (p symbol)
        | None ->
          let term = Env.term_of_id env id in
          let term_rewrite = rewrite term in
          not (Symbol.Set.for_all safe_symbol (symbols term_rewrite)))
      (0 -- (Env.dim env - 1))
    |> BatList.of_enum
  in

  (***************************************************************************
   * Find new non-linear terms to improve the projection
   ***************************************************************************)
  ensure_nonlinear_symbols (Env.ark wedge.env);
  let log = get_named_symbol ark "log" in

  let add_bound_unsafe bound =
    let abstract =
      Abstract0.meet_lincons_array
        (get_manager ())
        wedge.abstract
        [| lincons_of_atom env bound |]
    in
    wedge.abstract <- abstract
  in
  let add_bound precondition bound =
    logf ~level:`trace "Integrity: %a => %a"
      (Formula.pp ark) precondition
      (Formula.pp ark) bound;
    integrity (mk_or ark [mk_not ark precondition; bound]);

    ignore (lincons_of_atom env bound);

    update_env wedge;
    add_bound_unsafe bound
  in
  forget |> List.iter (fun id ->
      let term = Env.term_of_id env id in
      match Env.sd_term_of_id env id with
      | App (symbol, [base; x]) when symbol = log ->
        (* If 1 < base then
             lo <= x <= hi ==> log(base,lo) <= log(base, x) <= log(base,hi) *)
        begin
          match BatList.of_enum (V.enum base) with
          | [(base,base_id)] when base_id = Env.const_id
                               && QQ.lt QQ.one base ->
            let (lower, upper) = symbolic_bounds_vec wedge x forget in
            let x_term = Env.term_of_vec env x in
            let base_term = mk_real ark base in
            lower |> List.iter (fun lo ->
                add_bound
                  (mk_leq ark lo x_term)
                  (mk_leq ark (mk_app ark log [base_term; lo]) term));
            upper |> List.iter (fun hi ->
                add_bound
                  (mk_leq ark x_term hi)
                  (mk_leq ark term (mk_app ark log [base_term; hi])))
          | _ -> ()
        end
      | _ -> ());

  (***************************************************************************
   * Build environment of the projection and a translation into the projected
   * environment.
   ***************************************************************************)
  let substitution = ref [] in
  let new_env = Env.mk_empty ark in
  for id = 0 to Env.dim env - 1 do
    let dim = Env.dim_of_id env id in
    match symbol_of id with
    | Some symbol ->
      begin
        if p symbol then
          let rewrite_vec = Env.vec_of_term new_env (mk_const ark symbol) in
          substitution := (dim, rewrite_vec)::(!substitution)
      end
    | None ->
      let term = Env.term_of_id env id in
      let term_rewrite = rewrite term in
      if Symbol.Set.for_all safe_symbol (symbols term_rewrite) then

        (* Add integrity constraint for term = term_rewrite *)
        let precondition =
          Symbol.Set.enum (symbols term)
          |> BatEnum.filter_map (fun x ->
              if Symbol.Map.mem x rewrite_map then
                Some (mk_eq ark (mk_const ark x) (Symbol.Map.find x rewrite_map))
              else
                None)
          |> BatList.of_enum
          |> mk_and ark
        in
        integrity (mk_or ark [mk_not ark precondition;
                              mk_eq ark term term_rewrite]);

        let rewrite_vec = Env.vec_of_term new_env term_rewrite in
        substitution := (dim, rewrite_vec)::(!substitution)
  done;

  let abstract = forget_ids wedge.env wedge.abstract forget in

  (* Ensure abstract has enough dimensions to be able to interpret the
     substitution.  The substituion is interpreted within an implicit
     ("virtual") environment. *)
  let virtual_int_dim =
    max (Env.int_dim env) (Env.int_dim new_env)
  in
  let virtual_dim_of_id id =
    let open Env in
    match type_of_id new_env id with
    | `TyInt -> ArkUtil.search id new_env.int_dim
    | `TyReal -> virtual_int_dim + (ArkUtil.search id new_env.real_dim)
  in
  let virtual_linexpr_of_vec vec =
    let mk (coeff, id) =
      (coeff_of_qq coeff, virtual_dim_of_id id)
    in
    let (const_coeff, rest) = V.pivot Env.const_id vec in
    Linexpr0.of_list None
      (BatList.of_enum (BatEnum.map mk (V.enum rest)))
      (Some (coeff_of_qq const_coeff))
  in

  let abstract =
    let int_dims = Env.int_dim env in
    let real_dims = Env.real_dim env in
    let added_int = max 0 ((Env.int_dim new_env) - int_dims) in
    let added_real = max 0 ((Env.real_dim new_env) - real_dims) in
    let added =
      BatEnum.append
        ((0 -- (added_int - 1)) /@ (fun _ -> int_dims))
        ((0 -- (added_real - 1)) /@ (fun _ -> int_dims + real_dims))
      |> BatArray.of_enum
    in
    Abstract0.add_dimensions
      (get_manager ())
      abstract
      { Dim.dim = added;
        Dim.intdim = added_int;
        Dim.realdim = added_real }
      false
  in

  Log.logf ~level:`trace "Env (%d): %a"
    (List.length (!substitution))
    Env.pp new_env;
  List.iter (fun (dim, replacement) ->
      Log.logf ~level:`trace "Replace %a => %a"
        (Term.pp ark) (Env.term_of_id env (Env.id_of_dim env dim))
        (pp_vector new_env) replacement)
    (!substitution);

  let abstract =
    Abstract0.substitute_linexpr_array
      (get_manager ())
      abstract
      (BatArray.of_list (List.map fst (!substitution)))
      (BatArray.of_list (List.map (virtual_linexpr_of_vec % snd) (!substitution)))
      None
  in
  (* Remove extra dimensions *)
  let abstract =
    apron_set_dimensions
      (Env.int_dim new_env)
      (Env.real_dim new_env)
      abstract
  in
  let result =
    { env = new_env;
      int_dim = Env.int_dim new_env;
      real_dim = Env.real_dim new_env;
      abstract = abstract }
  in
  logf "Projection result: %a" pp result;
  result

let widen wedge wedge' =
  let ark = Env.ark wedge.env in
  let widen_env = Env.mk_empty ark in
  for id = 0 to (Env.dim wedge.env) - 1 do
    let term = Env.term_of_id wedge.env id in
    if Env.mem_term wedge'.env term then
      ignore (Env.vec_of_term widen_env term)
  done;

  (* Project onto intersected environment *)
  let project wedge =
    let forget = ref [] in
    let substitution = ref [] in
    for id = 0 to (Env.dim wedge.env) - 1 do
      let term = Env.term_of_id wedge.env id in
      let dim = Env.dim_of_id wedge.env id in
      if Env.mem_term widen_env term then
        substitution := (dim, Env.vec_of_term widen_env term)::(!substitution)
      else
        forget := dim::(!forget)
    done;
    let abstract =
      Abstract0.forget_array
        (get_manager ())
        wedge.abstract
        (Array.of_list (List.rev (!forget)))
        false
    in
    let abstract =
      Abstract0.substitute_linexpr_array
        (get_manager ())
        abstract
        (BatArray.of_list (List.map fst (!substitution)))
        (BatArray.of_list
           (List.map (Env.linexpr_of_vec widen_env % snd) (!substitution)))
        None
    in
    apron_set_dimensions
      (Env.int_dim widen_env)
      (Env.real_dim widen_env)
      abstract
  in
  let abstract = project wedge in
  let abstract' = project wedge' in
  { env = widen_env;
    int_dim = Env.int_dim widen_env;
    real_dim = Env.real_dim widen_env;
    abstract = Abstract0.widening (get_manager ()) abstract abstract' }

let farkas_equalities wedge =
  let open Lincons0 in
  let constraints =
    BatArray.enum (Abstract0.to_lincons_array (get_manager ()) wedge.abstract)
    |> BatEnum.filter_map (fun lcons ->
        match lcons.typ with
        | EQ -> Some lcons.linexpr0
        | _ -> None)
    |> BatArray.of_enum
  in
  let nb_columns =
    let dim = Abstract0.dimension (get_manager ()) wedge.abstract in
    (* one extra column for the constant *)
    dim.Dim.intd + dim.Dim.reald + 1
  in
  let columns =
    Array.init nb_columns (fun _ -> V.zero)
  in
  for row = 0 to Array.length constraints - 1 do
    constraints.(row) |> Linexpr0.iter (fun coeff col ->
        columns.(col) <- V.add_term (qq_of_coeff_exn coeff) row columns.(col));
    columns.(nb_columns - 1) <- V.add_term
        (qq_of_coeff_exn (Linexpr0.get_cst constraints.(row)))
        row
        columns.(nb_columns - 1)
  done;
  Array.mapi (fun id column ->
      let term =
        if id = (nb_columns - 1) then
          mk_real (Env.ark wedge.env) QQ.one
        else
          Env.term_of_id wedge.env id
      in
      (term, column))
    columns
  |> Array.to_list

let symbolic_bounds wedge symbol =
  let ark = Env.ark wedge.env in
  let vec = Env.vec_of_term ~register:false wedge.env (mk_const ark symbol) in
  match BatList.of_enum (V.enum vec) with
  | [(coeff, id)] ->
    assert (QQ.equal coeff QQ.one);

    let constraints =
      Abstract0.to_lincons_array (get_manager ()) wedge.abstract
    in
    BatEnum.fold (fun (lower, upper) lincons ->
        let open Lincons0 in
        let vec = Env.vec_of_linexpr wedge.env lincons.linexpr0 in
        let (a, t) = V.pivot id vec in
        if QQ.equal a QQ.zero then
          (lower, upper)
        else
          let bound =
            V.scalar_mul (QQ.negate (QQ.inverse a)) t
            |> Env.term_of_vec wedge.env
          in
          match lincons.typ with
          | EQ -> (bound::lower, bound::upper)
          | SUP | SUPEQ ->
            if QQ.lt QQ.zero a then
              (bound::lower, upper)
            else
              (lower, bound::upper)
          | _ -> (lower, upper)
      )
      ([], [])
      (BatArray.enum constraints)
  | _ -> assert false

let is_sat ark phi =
  let solver = Smt.mk_solver ark in
  let uninterp_phi =
    rewrite ark
      ~down:(nnf_rewriter ark)
      ~up:(Nonlinear.uninterpret_rewriter ark)
      phi
  in
  let (lin_phi, nonlinear) = ArkSimplify.purify ark uninterp_phi in
  let symbol_list = Symbol.Set.elements (symbols lin_phi) in
  let nonlinear_defs =
    Symbol.Map.enum nonlinear
    /@ (fun (symbol, expr) ->
        match refine ark expr with
        | `Term t -> mk_eq ark (mk_const ark symbol) t
        | `Formula phi -> mk_iff ark (mk_const ark symbol) phi)
    |> BatList.of_enum
  in
  let nonlinear = Symbol.Map.map (Nonlinear.interpret ark) nonlinear in
  let rec replace_defs_term term =
    substitute_const
      ark
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const ark x)
      term
  in
  let replace_defs =
    substitute_const
      ark
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const ark x)
  in
  solver#add [lin_phi];
  solver#add nonlinear_defs;
  let integrity psi =
    solver#add [Nonlinear.uninterpret ark psi]
  in
  let rec go () =
    match solver#get_model () with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat model ->
      let interp = Interpretation.of_model ark model symbol_list in
      match Interpretation.select_implicant interp lin_phi with
      | None -> assert false
      | Some implicant ->
        let constraints =
          of_atoms ark ~integrity (List.map replace_defs implicant)
        in
        if is_bottom constraints then
          go ()
        else
          `Unknown
  in
  go ()

let abstract ?exists:(p=fun x -> true) ark phi =
  logf "Abstracting formula@\n%a"
    (Formula.pp ark) phi;
  let solver = Smt.mk_solver ark in
  let uninterp_phi =
    rewrite ark
      ~down:(nnf_rewriter ark)
      ~up:(Nonlinear.uninterpret_rewriter ark)
      phi
  in
  let (lin_phi, nonlinear) = ArkSimplify.purify ark uninterp_phi in
  let symbol_list = Symbol.Set.elements (symbols lin_phi) in
  let nonlinear_defs =
    Symbol.Map.enum nonlinear
    /@ (fun (symbol, expr) ->
        match refine ark expr with
        | `Term t -> mk_eq ark (mk_const ark symbol) t
        | `Formula phi -> mk_iff ark (mk_const ark symbol) phi)
    |> BatList.of_enum
    |> mk_and ark
  in
  let nonlinear = Symbol.Map.map (Nonlinear.interpret ark) nonlinear in
  let rec replace_defs_term term =
    substitute_const
      ark
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const ark x)
      term
  in
  let replace_defs =
    substitute_const
      ark
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const ark x)
  in
  solver#add [lin_phi];
  solver#add [nonlinear_defs];
  let integrity psi =
    solver#add [Nonlinear.uninterpret ark psi]
  in
  let rec go wedge =
    let blocking_clause =
      to_formula wedge
      |> Nonlinear.uninterpret ark
      |> mk_not ark
    in
    logf ~level:`trace "Blocking clause %a" (Formula.pp ark) blocking_clause;
    solver#add [blocking_clause];
    match solver#get_model () with
    | `Unsat -> wedge
    | `Unknown ->
      logf ~level:`warn "Symbolic abstraction failed; returning top";
      top ark
    | `Sat model ->
      let interp = Interpretation.of_model ark model symbol_list in
      match Interpretation.select_implicant interp lin_phi with
      | None -> assert false
      | Some implicant ->
        let new_wedge =
          List.map replace_defs implicant
          (*          |> ArkSimplify.qe_partial_implicant ark p*)
          |> of_atoms ark ~integrity
          |> exists ~integrity p
        in
        go (join ~integrity wedge new_wedge)
  in
  let result = go (bottom ark) in
  logf "Abstraction result:@\n%a" pp result;
  result

let ensure_min_max ark =
  List.iter
    (fun (name, typ) ->
       if not (is_registered_name ark name) then
         register_named_symbol ark name typ)
    [("min", `TyFun ([`TyReal; `TyReal], `TyReal));
     ("max", `TyFun ([`TyReal; `TyReal], `TyReal))]

let symbolic_bounds_formula ?exists:(p=fun x -> true) ark phi symbol =
  ensure_min_max ark;
  let min = get_named_symbol ark "min" in
  let max = get_named_symbol ark "max" in
  let mk_min x y =
    match Term.destruct ark x, Term.destruct ark y with
    | `Real xr, `Real yr -> mk_real ark (QQ.min xr yr)
    | _, _ -> mk_app ark min [x; y]
  in
  let mk_max x y =
    match Term.destruct ark x, Term.destruct ark y with
    | `Real xr, `Real yr -> mk_real ark (QQ.max xr yr)
    | _, _ -> mk_app ark max [x; y]
  in

  let symbol_term = mk_const ark symbol in
  let subterm x = x != symbol in
  let solver = Smt.mk_solver ark in
  let uninterp_phi =
    rewrite ark
      ~down:(nnf_rewriter ark)
      ~up:(Nonlinear.uninterpret_rewriter ark)
      phi
  in
  let (lin_phi, nonlinear) = ArkSimplify.purify ark uninterp_phi in
  let symbol_list = Symbol.Set.elements (symbols lin_phi) in
  let nonlinear_defs =
    Symbol.Map.enum nonlinear
    /@ (fun (symbol, expr) ->
        match refine ark expr with
        | `Term t -> mk_eq ark (mk_const ark symbol) t
        | `Formula phi -> mk_iff ark (mk_const ark symbol) phi)
    |> BatList.of_enum
    |> mk_and ark
  in
  let nonlinear = Symbol.Map.map (Nonlinear.interpret ark) nonlinear in
  let rec replace_defs_term term =
    substitute_const
      ark
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const ark x)
      term
  in
  let replace_defs =
    substitute_const
      ark
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const ark x)
  in
  solver#add [lin_phi];
  solver#add [nonlinear_defs];
  let integrity psi =
    solver#add [Nonlinear.uninterpret ark psi]
  in
  let rec go (lower, upper) =
    match solver#get_model () with
    | `Unsat -> (lower, upper)
    | `Unknown ->
      logf ~level:`warn "Symbolic abstraction failed; returning top";
      ([[]], [[]])
    | `Sat model ->
      let interp = Interpretation.of_model ark model symbol_list in
      match Interpretation.select_implicant interp lin_phi with
      | None -> assert false
      | Some implicant ->
        let (wedge_lower, wedge_upper) =
          let wedge =
            of_atoms ark ~integrity (List.map replace_defs implicant)
            |> exists ~integrity ~subterm p
          in
          symbolic_bounds wedge symbol
        in
        let lower_blocking =
          List.map
            (fun lower_bound -> mk_lt ark symbol_term lower_bound)
            wedge_lower
          |> List.map (Nonlinear.uninterpret ark)
          |> mk_or ark
        in
        let upper_blocking =
          List.map
            (fun upper_bound -> mk_lt ark upper_bound symbol_term)
            wedge_upper
          |> List.map (Nonlinear.uninterpret ark)
          |> mk_or ark
        in
        solver#add [mk_or ark [lower_blocking; upper_blocking]];
        go (wedge_lower::lower, wedge_upper::upper)
  in
  let (lower, upper) = go ([], []) in
  let lower =
    if List.mem [] lower then
      None
    else
      Some (BatList.reduce mk_min (List.map (BatList.reduce mk_max) lower))
  in
  let upper =
    if List.mem [] upper then
      None
    else
      Some (BatList.reduce mk_max (List.map (BatList.reduce mk_min) upper))
  in
  (lower, upper)