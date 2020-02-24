module type S = sig
  type t
  type vertex
  
  type var
  type trans

  val mk_empty : unit -> t
  val add_vertex : t -> vertex -> unit
  val add_edge : t -> vertex -> trans -> vertex -> unit

  val set_vars : t -> vertex -> var list -> unit
  val set_max_vars : t -> vertex -> var list -> unit

  val live_vars : t -> (vertex -> var list)
  val havoc_vars : t -> (vertex -> var list)
  val havoc_live_vars : t -> (vertex -> var list)
end

module type Var = sig
  type t

  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val compare : t -> t -> int

  module Set : BatSet.S with type elt = t
end

module type Trans = sig
  type t
  type var

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit

  val guards : t -> var list
  val defines : t -> var list
  val havocs : t -> var list
  val uses : t -> var -> var list
end

module Make(V : Var)(T : Trans with type var = V.t) = struct
  type vertex = int
  type var = V.t
  type trans = T.t

  module G = Graph.Imperative.Digraph.ConcreteBidirectional(SrkUtil.Int)
  module HT = Hashtbl
  module VertSet = BatSet.Make(SrkUtil.Int)

  type t = {
    g : G.t;
    labels : (vertex * vertex, trans) HT.t;
    vars : (vertex, V.Set.t) HT.t;
    max : (vertex, V.Set.t) HT.t;
  }

  let mk_empty _ = {
    g = G.create ();
    labels = HT.create 991;
    vars = HT.create 991;
    max = HT.create 991;
  }

  let add_vertex va v =
    G.add_vertex va.g v

  let add_edge va u trans v =
    G.add_edge va.g u v;
    HT.replace va.labels (u,v) trans

  (* the set of live variables and defined variables is exactly SET(vars) *)
  let set_vars va v vars =
    HT.replace va.vars v (V.Set.of_list vars)

  (* restrict the live variables and defined variables to at most SET(vars) *)
  let set_max_vars va v vars =
    HT.replace va.max v (V.Set.of_list vars)

  (* Computes the set of live variables given the current graph and constraints *)
  let live_vars va =
    let module Live = Graph.Fixpoint.Make(G)
     (struct
        type vertex = G.E.vertex
        type edge = G.E.t
        type g = G.t
        type data = V.Set.t
        let direction = Graph.Fixpoint.Backward
        let equal = V.Set.equal
        let join = V.Set.union
        let analyze adj vars =
          let src = G.E.src adj in
          if HT.mem va.vars src then
            HT.find va.vars src
          else
            let dst = G.E.dst adj in
            let trans = HT.find va.labels (src, dst) in
            let defs = V.Set.of_list (T.defines trans) in
            let vars =
              V.Set.fold (fun var vars ->
                if V.Set.mem var defs then
                  V.Set.union (V.Set.of_list (T.uses trans var)) vars
                else
                  V.Set.add var vars
              ) vars (V.Set.of_list (T.guards trans))
            in
            if HT.mem va.max src then
              V.Set.inter vars (HT.find va.max src)
            else
              vars
      end)
    in
    let res = Live.analyze (fun v -> if HT.mem va.vars v then HT.find va.vars v else V.Set.empty) va.g in
    Memo.memo (fun v -> V.Set.to_list (res v))

  (* Computes the set of variables at each vertex that may not have been recently havoced consistent with the constraints *)
  let havoc_vars va =
    let module Havoc = Graph.Fixpoint.Make(G)
     (struct
        type vertex = G.E.vertex
        type edge = G.E.t
        type g = G.t
        type data = V.Set.t
        let direction = Graph.Fixpoint.Forward
        let equal = V.Set.equal
        let join = V.Set.union
        let analyze adj vars =
          let dst = G.E.dst adj in
          if HT.mem va.vars dst then
            HT.find va.vars dst
          else
            let trans = HT.find va.labels ((G.E.src adj), dst) in
            let defs =
              List.fold_left (fun defs v ->
                V.Set.union defs (V.Set.add v (V.Set.of_list (T.uses trans v))) (* defs u {v} u U{vars(e) : v <- e \in trans} *)
              ) (V.Set.union vars (V.Set.of_list (T.guards trans))) (T.defines trans)
            in
            V.Set.diff (if HT.mem va.max dst then V.Set.inter (HT.find va.max dst) defs else defs) (V.Set.of_list (T.havocs trans))
      end)
    in
    let res = Havoc.analyze (fun v -> if HT.mem va.vars v then HT.find va.vars v else V.Set.empty) va.g in
    Memo.memo (fun v -> V.Set.to_list (res v))

  (* Computes the set of variables that are both alive and have not been recently havoced *)
  let havoc_live_vars va =
    let lvars = live_vars va in
    let hvars = havoc_vars va in
    Memo.memo (fun v ->
      V.Set.to_list (V.Set.inter (V.Set.of_list (lvars v)) (V.Set.of_list (hvars v)))
    )

end
