open! Core
module Incr : Incremental.S = Incremental.Make ()

let post_incr ref =
  let result = !ref in
  Int.incr ref;
  result
;;

module type Abstract_set = sig
  type 'a t [@@deriving sexp]
  type 'a value

  type ('a, 'ret) ctx =
    mem:('a value -> 'a -> unit Incr.t) -> is_subset:('a -> 'a -> unit Incr.t) -> 'ret

  val mem : ('a, 'a value -> 'a t -> unit Incr.t) ctx
  val is_subset : ('a, 'a t -> 'a t -> unit Incr.t) ctx
end

module Value = struct
  module type Desc = sig
    type 'a t [@@deriving sexp]
  end

  module type S = sig
    type 'a t [@@deriving sexp]
    type 'a desc

    val create : 'a desc -> 'a t
    val desc : 'a t -> 'a desc
    val compare : _ t -> _ t -> int
  end

  module Make (X : Desc) : S with type 'a desc = 'a X.t = struct
    type 'a t =
      { id : int
      ; desc : 'a desc
      }

    and 'a desc = 'a X.t [@@deriving sexp]

    let id = ref 0
    let create desc = { id = post_incr id; desc }
    let desc t = t.desc
    let compare t1 t2 = Int.compare t1.id t2.id
  end
end

module Constraints
    (Value_desc : Value.Desc)
    (Abstract_set : Abstract_set with type 'a value := 'a Value.Make(Value_desc).t) =
struct
  type variable = int [@@deriving sexp, compare]

  let fresh =
    let next = ref 0 in
    fun () -> post_incr next
  ;;

  module Flow_set = struct
    type t =
      | Var of variable
      | Abstract of t Abstract_set.t
    [@@deriving sexp]
  end

  module Value = struct
    module T = struct
      include Value.Make (Value_desc)

      type nonrec t = Flow_set.t t [@@deriving sexp]

      let create : Flow_set.t desc -> t = create
    end

    include T
    include Comparable.Make (T)
  end

  type _ t =
    | Return : 'a -> 'a t (** [return x] *)
    | Map : 'a t * ('a -> 'b) -> 'b t (** [map t ~f] *)
    | True : unit t (** [true] *)
    | Conj : 'a t * 'b t -> ('a * 'b) t (** [C && C] *)
    | Exists : variable list * 'a t -> 'a t (** [exists a. C] *)
    | Subset : Flow_set.t * Flow_set.t -> unit t (** [s1 <= s2] *)
    | In : Value.t * Flow_set.t -> unit t (** [v in s] *)
    | Decode : variable -> Value.t list t (** [decode a] *)

  let rec sexp_of_t : type a. a t -> Sexp.t =
   fun t ->
    match t with
    | Return _ -> [%sexp Return]
    | Map (t, _) -> [%sexp Map, (t : t)]
    | True -> [%sexp True]
    | Conj (t1, t2) -> [%sexp Conj, (t1 : t), (t2 : t)]
    | Exists (vars, t) -> [%sexp Exists, (vars : variable list), (t : t)]
    | Subset (s1, s2) -> [%sexp Subset, (s1 : Flow_set.t), (s2 : Flow_set.t)]
    | In (value, s) -> [%sexp Value, (value : Value.t), (s : Flow_set.t)]
    | Decode var -> [%sexp Decode, (var : variable)]
 ;;

  include Applicative.Make (struct
    type nonrec 'a t = 'a t

    let return x = Return x
    let map = `Custom (fun t ~f -> Map (t, f))
    let apply t1 t2 = Map (Conj (t1, t2), fun (f, x) -> f x)
  end)

  (** [both t1 t2] is the conjunction of [t1] and [t2] -- explicitly redefined
      for performance reasons. *)
  let both t1 t2 = Conj (t1, t2)

  module Open_on_rhs_intf = struct
    module type S = sig end
  end

  module Let_syntax = struct
    let return = return

    include Applicative_infix

    module Let_syntax = struct
      let return = return
      let map = map
      let both = both

      module Open_on_rhs = struct end
    end
  end

  let ( <= ) s1 s2 = Subset (s1, s2)
  let ( &~ ) = both
  let ( >> ) t1 t2 = t1 &~ t2 >>| snd
  let decode a = Decode a

  let exists vars t =
    match vars with
    | [] -> t
    | vars ->
      (match t with
      | Exists (vars', t) -> Exists (vars @ vars', t)
      | t -> Exists (vars, t))
  ;;

  module Solver = struct
    exception Unbound_variable of variable

    module State = struct
      type t = { bindings : (variable, Value.Set.t Incr.Var.t) Hashtbl.t }

      let create () = { bindings = Hashtbl.create (module Int) }

      let bind t vars =
        List.iter vars ~f:(fun var ->
            let var' = Incr.Var.create Value.Set.empty in
            Hashtbl.set t.bindings ~key:var ~data:var')
      ;;

      let find t var =
        match Hashtbl.find t.bindings var with
        | Some values -> values
        | None -> raise (Unbound_variable var)
      ;;
    end

    let rec mem ~state value flow_set =
      let open Incr.Let_syntax in
      match flow_set with
      | Flow_set.Var var ->
        Incr.Var.replace (State.find state var) ~f:(fun values -> Set.add values value);
        return ()
      | Flow_set.Abstract abstract_set ->
        Abstract_set.mem
          ~is_subset:(is_subset ~state)
          ~mem:(mem ~state)
          value
          abstract_set

    and is_subset ~state flow_set1 flow_set2 =
      let open Incr.Let_syntax in
      match flow_set1, flow_set2 with
      | Var var1, Var var2 ->
        let%map values1 = Incr.Var.watch (State.find state var1) in
        Incr.Var.replace (State.find state var2) ~f:(Set.union values1)
      | Abstract _abstract_set, Var _var -> assert false
      | Var var, Abstract abstract_set ->
        let%bind values = Incr.Var.watch (State.find state var) in
        let%map _ =
          Set.fold values ~init:[] ~f:(fun acc value ->
              Abstract_set.mem
                ~is_subset:(is_subset ~state)
                ~mem:(mem ~state)
                value
                abstract_set
              :: acc)
          |> Incr.all
        in
        ()
      | Abstract abstract_set1, Abstract abstract_set2 ->
        Abstract_set.is_subset
          ~is_subset:(is_subset ~state)
          ~mem:(mem ~state)
          abstract_set1
          abstract_set2
    ;;

    let rec solve : type a. a t -> state:State.t -> a Incr.t =
     fun t ~state ->
      let open Incr.Let_syntax in
      match t with
      | Return x -> return x
      | Map (t, f) ->
        let%map t = solve t ~state in
        f t
      | True -> return ()
      | Conj (t1, t2) ->
        let%bind t1 = solve t1 ~state in
        let%map t2 = solve t2 ~state in
        t1, t2
      | Exists (vars, t) ->
        State.bind state vars;
        solve t ~state
      | Subset (s1, s2) -> is_subset ~state s1 s2
      | In (value, var) -> mem ~state value var
      | Decode var ->
        let values = State.find state var in
        Incr.Var.watch values >>| Set.to_list
   ;;

    type error = [ `Unbound_variable of variable ]

    let solve t =
      try
        let observer = solve t ~state:(State.create ()) |> Incr.observe in
        Incr.stabilize ();
        Ok (Incr.Observer.value_exn observer)
      with
      | Unbound_variable var -> Error (`Unbound_variable var)
    ;;
  end
end

module Example = struct
  module Parsetree = struct
    type expression =
      | Pexp_var of string
      | Pexp_fun of string * expression
      | Pexp_app of expression * expression
    [@@deriving sexp, compare]
  end

  open Parsetree

  module Value_desc = struct
    type 'a t =
      | Val_fun of
          { dom : 'a
          ; rng : 'a
          ; exp : string * expression
          }
    [@@deriving sexp]
  end

  module Value = Value.Make (Value_desc)

  module Abstract_set = struct
    type 'a t = Function of 'a * 'a [@@deriving sexp]
    type 'a value = 'a Value.t

    type ('a, 'ret) ctx =
      mem:('a value -> 'a -> unit Incr.t) -> is_subset:('a -> 'a -> unit Incr.t) -> 'ret

    let mem ~mem:_ ~is_subset value abstract_set =
      let open Incr.Let_syntax in
      match Value.desc value, abstract_set with
      | Val_fun { dom; rng; _ }, Function (dom', rng') ->
        let%bind () = is_subset dom' dom in
        is_subset rng rng'
    ;;

    let is_subset ~mem:_ ~is_subset t1 t2 =
      let open Incr.Let_syntax in
      match t1, t2 with
      | Function (dom, rng), Function (dom', rng') ->
        let%bind () = is_subset dom' dom in
        is_subset rng rng'
    ;;
  end

  module Constraints = Constraints (Value_desc) (Abstract_set)

  module Env = struct
    type t = (string, Constraints.variable) List.Assoc.t

    let empty : t = []
    let find t var = List.Assoc.find_exn t var ~equal:String.equal
    let bind t ~var ~flow_set = List.Assoc.add t var flow_set ~equal:String.equal
  end

  let rec generate_exp ~env exp exp_flow_set =
    let open Constraints in
    match exp with
    | Pexp_var var -> Var (Env.find env var) <= Var exp_flow_set
    | Pexp_app (exp1, exp2) ->
      let a1 = fresh () in
      let a2 = fresh () in
      exists
        [ a1; a2 ]
        (generate_exp ~env exp1 a1
        >> generate_exp ~env exp2 a2
        >> (Var a1 <= Abstract (Function (Var a2, Var exp_flow_set))))
    | Pexp_fun (var, exp) ->
      let a1 = fresh () in
      let a2 = fresh () in
      let env = Env.bind env ~var ~flow_set:a1 in
      let value : Constraints.Value.t =
        Constraints.Value.create (Val_fun { dom = Var a1; rng = Var a2; exp = var, exp })
      in
      exists [ a1; a2 ] (In (value, Var exp_flow_set) >> generate_exp ~env exp a2)
  ;;

  let cfa exp =
    let open Constraints in
    let a = fresh () in
    let constraint_ = exists [ a ] (generate_exp ~env:Env.empty exp a >> decode a) in
    Solver.solve constraint_
  ;;

  let print_result exp =
    let result = cfa exp in
    let output =
      match result with
      | Ok values ->
        values
        |> List.map ~f:(fun value ->
               match Constraints.Value.desc value with
               | Val_fun { exp = var, exp; _ } -> Parsetree.Pexp_fun (var, exp))
        |> [%sexp_of: Parsetree.expression list]
      | Error (`Unbound_variable var) -> [%message "Unbound variable" (var : int)]
    in
    output |> Sexp.to_string_hum |> print_endline
  ;;
end

let () =
  let open Example in
  print_result (Pexp_fun ("x", Pexp_var "x"))
;;
