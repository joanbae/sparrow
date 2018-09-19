(** Interactive CLI debug mode. *)

(** The type of a query.

    The query is simply regarded as an {e on-demand} tree constructed
    by the two types of query.

    - {b String query} contains a string message to print.

    - {b Option query} contains a set of options generating queries to
      traverse next time.

    {e On-demand} tree construction: since each option has a function
    to generate the next query, rather than having the next query
    itself, the query tree is constructed when necessary during the
    debug mode.
*)
type t

(** Start the debug mode. *)
val run : t -> unit

(** {2 String query} *)

(** Return a string query. *)
val short : string -> t

(** [long f] returns a string query to print a long message.  When
    running the query, [f ()] is called to print a long message, or to
    make a side effect, e.g., writing data to a file. *)
val long : (unit -> unit) -> t

(** {2 Option query} *)

(** The type of a set of options. *)
type options_t

(** Return an empty set of options. *)
val empty : options_t

(** [add name gen options] adds an option to [options].

    - [name] is the name of the option.  The first substring
      parenthesized by [\[] and [\]] of [name] is used as a command in
      the debug mode.  If there is no such a substring, an arbitrary
      number is assigned as a command.

    - [gen] is a function to generate an actual query to traverse.
      The arguments given with the command are passed to [gen].

    For example, if an option is add by [add "\[n\]ame" gen], and
    input the following command in the debug mode,

    {[$ n arg1 arg2]}

    the next query is generated by [gen \["arg1"; "arg2"\]].
*)
val add : ?do_shortcut:bool -> string -> (string list -> t) -> options_t -> options_t

(** Finalize and return an option query. *)
val final : options_t -> t
