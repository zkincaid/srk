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

module Make(V : Var)(T : Trans with type var = V.t) : S with type vertex = int and
                                                             type var = V.t and
                                                             type trans = T.t
