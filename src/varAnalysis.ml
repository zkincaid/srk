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
  val set_pooling : t -> vertex -> bool -> unit

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
    mutable pool : VertSet.t;
  }

  let mk_empty _ = {
    g = G.create ();
    labels = HT.create 991;
    vars = HT.create 991;
    max = HT.create 991;
    pool = VertSet.empty;
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

  (* For defined variable analysis, this causes v to act as a join rather than meet *)
  let set_pooling va v b =
    if b then
      va.pool <- VertSet.add v va.pool
    else
      va.pool <- VertSet.remove v va.pool

  (* Work list algorithm ---
     g : graph of interest
     q : Queue of initial locations
     f : update function
     next : what nodes to process next
   *)
  let work_list g q f next =
    while not (Queue.is_empty q) do
      let v = Queue.pop q in
      List.iter (fun adj ->
        f q v adj
      ) (next g v)
    done

  (* Computes the set of live variables given the current graph and constraints *)
  let live_vars va =
    let avars = HT.copy va.vars in
    G.iter_vertex (fun v ->
      if not (HT.mem avars v) then
        HT.add avars v V.Set.empty
    ) va.g;
    let alive q v adj =
      let src = G.E.src adj in
      let vars =
        if HT.mem va.vars src then (* If src is a constant value *)
          HT.find va.vars src (* Do nothing, keep the same value *)
        else
          let trans = HT.find va.labels (src, v) in
          let defs = V.Set.of_list (T.defines trans) in
          let vars =
            V.Set.fold (fun var vars ->
              if V.Set.mem var defs then
                V.Set.union (V.Set.of_list (T.uses trans var)) vars
              else
                V.Set.add var vars
            ) (HT.find avars v) (V.Set.of_list (T.guards trans))
          in
          if HT.mem va.max src then
            V.Set.inter vars (HT.find va.max src)
          else
            vars
      in
      if not (V.Set.subset vars (HT.find avars src)) then
        begin
          HT.replace avars src vars;
          Queue.add src q
        end
    in
    let q = Queue.create () in
    G.iter_vertex (fun v -> Queue.add v q) va.g;
    work_list va.g q alive G.pred_e;
    Memo.memo (fun v -> V.Set.to_list (HT.find avars v))

  (* Havoc analysis where we start at (vars v) for each vertex *)
  let havoc_vars' va vars =
    let dvars = HT.create 991 in
    G.iter_vertex (fun v ->
      HT.add dvars v (V.Set.of_list (vars v))
    ) va.g;
    let defined q v adj =
      let dst = G.E.dst adj in
      let dv = HT.find dvars dst in
      let vars =
        if HT.mem va.vars dst then (* If dst is a constant value *)
          dv (* Do not change the value *)
        else
          let get_defined src dst vars =
            let trans = HT.find va.labels (src, dst) in
            let defs =
              List.fold_left (fun defs v ->
                V.Set.union defs (V.Set.add v (V.Set.of_list (T.uses trans v))) (* defs u {v} u U{vars(e) : v <- e \in trans} *)
              ) (V.Set.union vars (V.Set.of_list (T.guards trans))) (T.defines trans)
            in
            V.Set.diff defs (V.Set.of_list (T.havocs trans))
          in
          V.Set.inter dv
           (if VertSet.mem dst va.pool then
              List.fold_left (fun defs adj ->
                V.Set.union defs (get_defined (G.E.src adj) dst (HT.find dvars (G.E.src adj)))
              ) V.Set.empty (G.pred_e va.g dst)
            else
              get_defined v dst (HT.find dvars v)
           )
      in
      if not (V.Set.subset dv vars) then (* strict subset : Note by construction vars <= dv *)
        begin
          HT.replace dvars dst vars;
          Queue.add dst q
        end
    in
    let q = Queue.create () in
    G.iter_vertex (fun v -> Queue.add v q) va.g;
    work_list va.g q defined G.succ_e;
    Memo.memo (fun v -> V.Set.to_list (HT.find dvars v))

  (* Computes the set of variables not recently havoced given the current graph and constraints *)
  let havoc_vars va =
    let all_vars =
      HT.fold (fun _ vars avars ->
        V.Set.union vars avars
      ) va.vars (
        HT.fold (fun _ max avars ->
          V.Set.union max avars
        ) va.max (
          HT.fold (fun _ trans avars ->
            let guards = V.Set.of_list (T.guards trans) in
            let defs = V.Set.of_list (T.defines trans) in
            V.Set.fold (fun d vars ->
              V.Set.union vars (V.Set.of_list (T.uses trans d))
            ) defs (V.Set.union defs guards)
          ) va.labels V.Set.empty
        )
      )
    in
    havoc_vars' va (fun v ->
      V.Set.to_list (
        if HT.mem va.vars v then
          HT.find va.vars v
        else if G.in_degree va.g v = 0 then
          V.Set.empty
        else if HT.mem va.max v then
          HT.find va.max v
        else
          all_vars
      )
    )

  (* Computes the set of variables that are both alive and have not been recently havoced *)
  let havoc_live_vars va =
    let vars = live_vars va in
    havoc_vars' va (fun v ->
      if (G.in_degree va.g v = 0) && (not (HT.mem va.vars v)) then
        []
      else
        (vars v)
    )

end
