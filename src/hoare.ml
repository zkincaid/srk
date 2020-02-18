open Syntax
open Transition
open SrkZ3
open BatPervasives

include Log.Make(struct let name = "srk.hoare" end)

module type Letter = sig
  type t
  type trans
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
  val transition_of : t -> trans
end

module MakeSolver(Ctx : Syntax.Context) (Var : Transition.Var) (Ltr : Letter with type trans = Transition.Make(Ctx)(Var).t) = struct

  module Infix = Syntax.Infix(Ctx)
  module Transition = Transition.Make(Ctx)(Var)

  type transition = Ltr.trans
  type formula = Ctx.formula
  type triple = (formula list) * Ltr.t * (formula list)

  module DA = BatDynArray

  let srk = Ctx.context

  let pp_triple formatter (pre, ltr, post) =
    let open Format in
    fprintf formatter "{";
    SrkUtil.pp_print_enum ~pp_sep:(fun formatter () -> fprintf formatter " /\\ ")
                          (Expr.pp srk)
                          formatter
                          (BatList.enum pre);
    fprintf formatter "} ";
    Ltr.pp formatter ltr;
    fprintf formatter " {";
    SrkUtil.pp_print_enum ~pp_sep:(fun formatter () -> fprintf formatter " /\\ ")
                          (Expr.pp srk)
                          formatter
                          (BatList.enum post);
    fprintf formatter "}"

  type t = {
      mutable solver : Ctx.t CHC.solver;
      triples : triple DA.t;
    }

  let mk_solver () =
    { solver = CHC.mk_solver srk;
      triples = DA.create();
    }

  let get_solver solver =
    solver.solver

  (*
     register {[P(...) ; Q(...); x = 3; y < x]} transition {[R(...); S(...)]}
     as P(...) /\ Q(...) /\ x = 3 /\ y < x /\ transition.guard --> R(...)
        P(...) /\ Q(...) /\ x = 3 /\ y < x /\ transition.guard --> S(...)
   *)
  let register_triple solver (pre, ltr, post) =
    (* logf ~level:`always "%a" pp_triple (pre, ltr, post); *)
    let rec register_formulas formulas =
      match formulas with
      | [] -> ()
      | form :: forms ->
         begin
           match destruct srk form with
           | `App (p, _) -> CHC.register_relation solver.solver p
           | _ -> ()
         end; register_formulas forms
    in
    let fresh =
      let ind : int ref = ref (-1) in
      Memo.memo (fun sym ->
          match typ_symbol srk sym with
          | `TyInt  -> incr ind; mk_var srk (!ind) `TyInt
          | `TyReal -> incr ind; mk_var srk (!ind) `TyReal
          | `TyBool -> incr ind; mk_var srk (!ind) `TyBool
          | _ -> mk_const srk sym
        )
    in
    let trans = Ltr.transition_of ltr in
    let body = (* conjunct all preconditions and guard of the transition *)
      let rec go rels =
        match rels with
        | [] -> substitute_const srk fresh (Transition.guard trans)
        | rel :: rels -> mk_and srk [(substitute_const srk fresh rel); go rels]
      in go pre
    in
    let add_rules posts =
      let postify sym = 
        match Var.of_symbol sym with
        | Some v when Transition.mem_transform v trans ->
             substitute_const srk fresh (Transition.get_transform v trans)
        | _ -> fresh sym
      in
      let rec go posts = (* add a rule for each post condition *)
        match posts with
        | [] -> ()
        | post :: posts -> CHC.add_rule solver.solver body (substitute_const srk postify post); go posts
      in
      go posts
    in
    DA.add solver.triples (pre, ltr, post);
    register_formulas pre;
    register_formulas post;
    add_rules post

  let check_solution solver = CHC.check solver.solver

  let get_solution solver =
    let get_triple trips (pre, ltr, post) =
      let rec subst =
        let rewriter expr =
          match destruct srk expr with
          | `App (rel, args) when (match (typ_symbol srk rel) with | `TyFun _ -> true | _ -> false) ->
             (substitute srk
                (fun v -> List.nth args v)
                (CHC.get_solution solver.solver rel) :> ('a, typ_fo) Syntax.expr)
          | _ -> expr
        in
        function
        | [] -> []
        | rel :: rels ->
           (rewrite srk ~down:rewriter rel) :: (subst rels)
      in
      (subst pre, ltr, subst post) :: trips
    in
    List.rev (DA.fold_left get_triple [] solver.triples)

  let get_symbolic solver =
    DA.to_list solver.triples

  let verify_solution solver =
    match CHC.check solver.solver with
    | `Sat ->
       List.fold_left (fun ret (pre, ltr, post) ->
           match ret with
           | `Invalid -> `Invalid
           | x ->
              match (Transition.valid_triple (Ctx.mk_and pre) [Ltr.transition_of ltr] (Ctx.mk_and post)) with
              | `Valid -> x
              | y -> y
         ) `Valid (get_solution solver)
    | `Unsat -> `Invalid
    | `Unknown -> `Unknown

  (* Useful functions for simplify and reduce vars *)
  let rec conjuncts phi =
    match Syntax.destruct srk phi with
    | `Tru -> []
    | `And conjs -> List.flatten (List.map conjuncts conjs)
    | _ -> [phi]
      
  let mk_and conjs =
    match conjs with
    | [] -> Ctx.mk_true
    | [phi] -> phi
    | _ -> Ctx.mk_and (List.flatten (List.map conjuncts conjs))

  (* takes a triple and creates a new hoare triple for each conjunct of the post post.
     Then removes irrelevant pre conditions using unsat core *)
  let simplify (pre, letter, post) =
    let pre = conjuncts (mk_and pre) in
    let post = conjuncts (mk_and post) in
    (* Minimal pre condition for post and transition's guard by finding unsat core of:
       ~(pre /\ guard => post) <==> pre /\ guard /\ ~post *)
    let min_pre post =
      let trans = Ltr.transition_of letter in
      (* Substitute var with it's expression if it appears in the transform *)
      let subst_assign phi =
        let subst sym =
          match Var.of_symbol sym with
          | Some v when Transition.mem_transform v trans -> (Transition.get_transform v trans)
          | _ -> Ctx.mk_const sym
        in
        (substitute_const srk subst phi)
      in
      let post_ass = subst_assign post in
      match pre, (Syntax.destruct srk post_ass) with
      | [], _ -> [Ctx.mk_true]
      | _, `Tru -> [Ctx.mk_true]
      | _, _ ->
         begin
           let z3_solver = SrkZ3.mk_solver srk in
           let assumptions = List.map (fun _ -> Ctx.mk_const (Ctx.mk_symbol `TyBool)) pre in
           let rules = List.map2 (fun pre ass -> Syntax.mk_iff srk pre ass) pre assumptions in
           Solver.add z3_solver ((Ctx.mk_not post_ass) :: (Transition.guard trans) :: rules);
           let rec get_pres ass pres core acc =
             match ass, pres, core with
             | a :: ass, p :: pres, c :: core ->
                begin
                  if (a = c) then
                    get_pres ass pres core (p :: acc)
                  else
                    get_pres ass pres (c :: core) acc
                end
             | _, _, [] -> acc
             | [], p, c -> assert false
             | a, [], c -> assert false
           in
           match Solver.get_unsat_core z3_solver assumptions with
           | `Sat -> assert false
           | `Unknown -> pre
           | `Unsat core -> get_pres assumptions pre core []
         end
    in
    let rec split posts acc =
      match posts with
      | [] -> acc
      | post :: posts ->
         split posts (((min_pre post), letter, [post]) :: acc)
    in
    split post []

  (* This function assumes that for each occurenceo of R in hoare triples
     R is applied to the same sequence of variables
   *)
  let reduce_vars solver =
    (* Translate the Srk.Transition module into one that satisfies the Srk.VarAnalysis.Transition requirements *)
    let module Var = struct
      include Var
      module Set = BatSet.Make(Var)
     end
    in
    let module Trans = struct
      module T = Transition
      include T

      let guards trans =
        Symbol.Set.fold (fun sym vars ->
          match Var.of_symbol sym with
          | Some v -> v :: vars
          | _ -> vars
        ) (symbols (T.guard trans)) []

      let defines trans = T.defines trans

      let havocs trans =
        BatEnum.fold (fun vars (var, exp) ->
          match destruct Ctx.context exp with
          | `App (sym, []) ->
            begin
              match Var.of_symbol sym with
              | None when not (Symbol.Set.mem sym (symbols (T.guard trans))) -> var :: vars
              | _ -> vars
            end
          | _ -> vars
        ) [] (T.transform trans)

      let uses trans var =
        Symbol.Set.fold (fun sym vars ->
          match Var.of_symbol sym with
          | Some v -> v :: vars
          | _ -> vars
        ) (symbols (T.get_transform var trans)) []
     end
    in
    (* Function to translate from preds / expressions to locations / variables *)
    (* Turn a predicate into a location (int) *)
    let to_loc =
      let next_loc : int ref = ref (-1) in
      Memo.memo (fun pred -> incr next_loc; !next_loc)
    in
    (* Get variables of an expression by using get symbols *)
    let vars_of expr =
      Symbol.Set.fold (fun sym vars ->
          match Var.of_symbol sym with
          | Some v -> Var.Set.add v vars
          | None -> vars
        ) (symbols expr) Var.Set.empty
    in
    (* Translate Hoare Triples into VarAnalysis constraint graph *)
    let module VA = VarAnalysis.Make(Var)(Trans) in
    let va = VA.mk_empty () in
    let add_vars pred =
      match destruct srk pred with
      | `App _ -> VA.set_max_vars va (to_loc pred) (Var.Set.to_list (vars_of pred))
      | _ -> VA.set_vars va (to_loc pred) (Var.Set.to_list (vars_of pred))
    in
    DA.iter (fun (pres, letter, posts) ->
      let pre = mk_and pres in
      let pre_loc = to_loc pre in
      VA.add_vertex va pre_loc;
      VA.set_pooling va pre_loc true;
      (match pres with
       | _ :: _ :: _ ->
         VA.set_max_vars va pre_loc (Var.Set.to_list (vars_of pre));
         List.iter (fun pred ->
           VA.add_vertex va (to_loc pred);
           add_vars pred;
           VA.add_edge va (to_loc pred) Transition.one pre_loc
         ) pres
       | _ ->
         VA.set_pooling va pre_loc false;
         add_vars pre
      );
      List.iter (fun post ->
        VA.add_vertex va (to_loc post);
        add_vars post;
        VA.add_edge va pre_loc (Ltr.transition_of letter) (to_loc post)
      ) posts
    ) solver.triples;
    let new_vars pred =
      let vars = VA.havoc_live_vars va in
      vars (to_loc pred)
    in
    let trips =
      let f =
        Memo.memo (fun pred ->
          let get_pred var_types = Ctx.mk_symbol (`TyFun (var_types, `TyBool)) in
          match destruct srk pred with
          | `App _ ->
            begin
              let vars = new_vars pred in
              let vars_type = List.map (fun v -> (Var.typ v :> typ_fo)) vars in
              let vars_const = List.map (fun v -> Ctx.mk_const (Var.symbol_of v)) vars in
              Ctx.mk_app (get_pred vars_type) vars_const
            end
          | _ -> pred
        )
      in
      DA.map (fun (pre, letter, post) ->
        let pre = List.map f pre in
        let post = List.map f post in
        (pre, letter, post)
      ) solver.triples
    in
    DA.clear solver.triples;
    solver.solver <- CHC.mk_solver srk;
    DA.iter (fun trip -> register_triple solver trip) trips

end
