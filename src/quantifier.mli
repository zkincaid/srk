open Syntax
open Interpretation

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

  (** pretty prints a normalized formula *)
  val pp_normal : 'a context -> Format.formatter -> 'a normalized_formula -> unit
end

type 'a cg_formula = ([`Forall | `Exists] * symbol) list * 'a formula
type 'a fg_formula = [ `Forall of symbol * 'a fg_formula
                     | `Exists of symbol * 'a fg_formula
                     | `And of 'a fg_formula list
                     | `Or of 'a fg_formula list
                     | `Atom of 'a formula ]

type 'a fg_skeleton = [ `Forall of symbol * 'a fg_skeleton
                      | `Exists of symbol * (('a, typ_fo) expr * 'a fg_skeleton) list
                      | `Or of (int * 'a fg_skeleton) list (* a partial function mapping from disjuncts to the respective strategy *)
                      | `And of 'a fg_skeleton list (* a strategy for each conjunct *)
                      | `Empty ]

(** A Coarse-Grain Strategy is a strategy the separates the formula into
    its quantifier prefix and its matrix. The Coarse-Grain game plays only
    over the quantifier prefix.
    The normalization of a formula is its prefix form (quantifier prefix + matrix) *)
module CoarseGrainStrategyImprovement :
    StrategyImprovement with type 'a normalized_formula = 'a cg_formula
                         and type 'a move = [ `Forall of symbol | `Exists of symbol * ('a, typ_fo) expr ]

(** A Fine-Grain Strategy is a strategy for a game the plays over the entire formula:
    quantifiers, conjunction, and disjunction. Formulas are normalized to push
    all negations into the atoms *)
module FineGrainStrategyImprovement :
    StrategyImprovement with type 'a normalized_formula = 'a fg_formula
                         and type 'a move = [ `Forall of symbol
                                            | `Exists of symbol * ('a, typ_fo) expr
                                            | `Or of int
                                            | `And of int ]
                         and type 'a skeleton = 'a fg_skeleton

(** Pushes quantifiers further into expression tree. Does not preserve
 * quantifier ordering. May eliminate unused quantifiers.*)
val miniscope : 'a context -> 'a formula -> 'a formula

val normalize : 'a context -> 'a formula -> ([`Forall | `Exists] * symbol) list * 'a formula

(** Quantifier eliminiation via model-based projection *)
val qe_mbp : 'a context -> 'a formula -> 'a formula

(** Model-based projection.  If [dnf] option is set, convert to
   disjunctive normal form. *)
val mbp : ?dnf:bool -> 'a context -> (symbol -> bool) -> 'a formula -> 'a formula

(** Over-approximtate model-based projection.  If [dnf] option is set,
   convert to disjunctive normal form. *)
val mbp_cover : ?dnf:bool -> 'a context -> (symbol -> bool) -> 'a formula -> 'a formula

val is_presburger_atom : 'a context -> 'a formula -> bool

(** Given an interpretation [M], a conjunctive formula [cube] such
   that [M |= cube], and a predicate [p], find a cube [cube']
   expressed over symbols that satisfy [p] such that [M |= cube' |=
   cube].  [local_project_cube] has a finite image in the sense that
   for any cube [c], the set [{ local_project_cube srk p m c : m |= c
   }] is finite.  [local_project_cube] assumes a formula in [QF_LRA];
   if not, then [cube'] may not entail [cube], but it is guaranteed to
   be satisfied by [M]. *)
val local_project_cube : 'a context ->
  (symbol -> bool) ->
  'a interpretation ->
  'a formula list ->
  'a formula list
