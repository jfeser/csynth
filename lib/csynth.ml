open! Core

module ZZ3 = Z3overlay.Make (struct
  let ctx = Z3.mk_context [("proof", "true")]
end)

open ZZ3

module Component = struct
  type t =
    { name: string
    ; id: int
    ; inputs: Type.Wrapped.t list
    ; output: Type.Wrapped.t
    ; constr: zuntyped Term.t list -> zuntyped Term.t -> zbool Term.t }

  let name {name; id; _} = sprintf "%s_%d" name id

  let ivar c i n =
    let t = List.nth_exn c.inputs i in
    let name = sprintf "%s_arg_%d/%d" (name c) i n in
    Type.Wrapped.unwrap
      {run= (fun t -> Symbol.declare t name |> Term.symbol |> Term.magic)}
      t

  let ovar c n =
    let name = sprintf "%s_ret/%d" (name c) n in
    Type.Wrapped.unwrap
      {run= (fun t -> Symbol.declare t name |> Term.symbol |> Term.magic)}
      c.output

  let constr cs n =
    List.map cs ~f:(fun c ->
        c.constr
          (List.init (List.length c.inputs) ~f:(fun i -> ivar c i n))
          (ovar c n))
    |> Term.and_

  let iloc c i = Symbol.declare Int (sprintf "l_%s_arg_%d" (name c) i)

  let oloc c = Symbol.declare Int (sprintf "l_%s_ret" (name c))

  let ilocs c = List.init (List.length c.inputs) ~f:(iloc c)

  let locs cs = List.concat_map cs ~f:(fun c -> oloc c :: ilocs c)

  let add id =
    { name= "add"
    ; id
    ; inputs= Type.[Wrapped.wrap Int; Wrapped.wrap Int]
    ; output= Type.(Wrapped.wrap Int)
    ; constr=
        (fun ins out ->
          match ins with
          | [i1; i2] -> Term.(magic i1 + magic i2 = magic out)
          | _ -> assert false) }

  let one id =
    { name= "one"
    ; id
    ; inputs= []
    ; output= Type.(Wrapped.wrap Int)
    ; constr= (fun _ out -> Term.(int 1 = magic out)) }
end

module Spec = struct
  type t =
    { inputs: Type.Wrapped.t list
    ; output: Type.Wrapped.t
    ; constr: zuntyped Term.t list -> zuntyped Term.t -> zbool Term.t }

  let ivar c i =
    let t = List.nth_exn c.inputs i in
    let name = sprintf "in_%d" i in
    Type.Wrapped.unwrap
      {run= (fun t -> Symbol.declare t name |> Term.symbol |> Term.magic)}
      t

  let ivars c = List.init (List.length c.inputs) ~f:(ivar c)

  let ovar c n =
    let name = sprintf "out/%d" n in
    Type.Wrapped.unwrap
      {run= (fun t -> Symbol.declare t name |> Term.symbol |> Term.magic)}
      c.output

  let constr c n =
    c.constr (List.init (List.length c.inputs) ~f:(ivar c)) (ovar c n)

  let iloc i = Term.int i

  let oloc m = Term.int (m - 1)

  let ninputs s = List.length s.inputs
end

module Program = struct
  type t = (Component.t * [`Input of int | `Var of int] list) list

  let of_model m lib spec : t =
    List.map lib ~f:(fun c ->
        let args =
          List.map (Component.ilocs c) ~f:(fun v ->
              let l = Model.get_value ~model:m v |> Z.to_int in
              if l < Spec.ninputs spec then `Input l
              else `Var (l - Spec.ninputs spec))
        in
        let out = Model.get_value ~model:m (Component.oloc c) |> Z.to_int in
        (out, (c, args)))
    |> List.sort ~compare:(fun (x1, _) (x2, _) -> [%compare: int] x1 x2)
    |> List.map ~f:(fun (_, x) -> x)

  let to_string (p : t) =
    let args_to_string a =
      List.map a ~f:(function
        | `Input x -> sprintf "i%d" x
        | `Var x -> sprintf "x%d" x)
      |> String.concat ~sep:" "
    in
    List.mapi p ~f:(fun i (c, args) ->
        sprintf "x%d = %s %s" i c.Component.name (args_to_string args))
    |> String.concat ~sep:"\n"
end

(** Generate a well-formedness constraint. This constraint combines the
   consistency, acyclicity, and location range constraints. This constraint only
   refers to the location variables. *)
let well_formed lib ninputs =
  let open Component in
  let consistent = Term.(distinct (List.map lib ~f:(fun c -> !(oloc c)))) in
  let acyclic =
    List.concat_map lib ~f:(fun c ->
        List.init (List.length c.inputs) ~f:(fun i ->
            Term.(!(iloc c i) < !(oloc c))))
    |> Term.and_
  in
  let nlines = List.length lib + ninputs in
  (* Parameters can refer to any input and any intermediate value. *)
  let param_range =
    Term.(
      List.concat_map lib ~f:(fun c ->
          List.init (List.length c.inputs) ~f:(fun i ->
              int 0 <= !(iloc c i) && !(iloc c i) < int nlines))
      |> and_)
  in
  (* Outputs can only be intermediate values. *)
  let ret_range =
    Term.(
      List.map lib ~f:(fun c -> int ninputs <= !(oloc c) && !(oloc c) < int nlines)
      |> and_)
  in
  Term.(consistent && acyclic && param_range && ret_range)

(** Generate a connnection constraint. This constraint links location variables
   and value variables. It uses fresh value variables for the library
   input/outputs and for the outputs but the inputs are fixed. *)
let connection n lib spec =
  let m = List.length lib + List.length spec.Spec.inputs in
  let pairs =
    Spec.(
      (oloc m, ovar spec n)
      :: List.init (List.length spec.inputs) ~f:(fun i -> (iloc i, ivar spec i)))
    @ List.concat_map lib ~f:(fun c ->
          Component.(
            (Term.(!(oloc c)), ovar c n)
            :: List.init (List.length c.inputs) ~f:(fun i ->
                   (Term.(!(iloc c i)), ivar c i n))))
  in
  List.concat_map pairs ~f:(fun (l1, t1) ->
      List.filter_map pairs ~f:(fun (l2, t2) ->
          if Term.O.(l1 = l2 && t1 = t2) then None
          else Some Term.(l1 = l2 ==> (t1 = t2))))
  |> Term.and_

let subst_vars model vars term =
  let sub =
    List.map vars ~f:(fun v -> (Term.magic v, Term.magic (Model.eval ~model v)))
  in
  Term.subst term sub

let solve max_n lib spec =
  let solver = Solver.make () in
  let well_formed_constr = well_formed lib (List.length spec.Spec.inputs) in
  Solver.add ~solver well_formed_constr ;
  let verifier = Solver.make () in
  Solver.add ~solver:verifier (Component.constr lib 0) ;
  Solver.add ~solver:verifier Term.(not (Spec.constr spec 0)) ;
  let conn_constr = connection 0 lib spec in
  let rec loop n =
    if n > max_n then Or_error.errorf "Synthesis failed: Max iterations exceeded"
    else
      match Solver.(check ~solver []) with
      | Unsat proof ->
          Or_error.errorf "Synthesis failed: %s" (Term.to_string (Lazy.force proof))
      | Unknown e -> Or_error.errorf "Synthesis failed: %s" e
      | Sat model -> (
          let conn_constr =
            subst_vars (Lazy.force model)
              (Component.locs lib |> List.map ~f:Term.( ! ))
              conn_constr
            |> Term.magic
          in
          match Solver.(check ~solver:verifier [conn_constr]) with
          | Unsat _ -> Ok (Program.of_model (Lazy.force model) lib spec)
          | Unknown e -> Or_error.errorf "Synthesis failed: %s" e
          | Sat model ->
              let csynth =
                let cspec = Spec.constr spec n in
                let cconn = connection n lib spec in
                let clib = Component.constr lib n in
                subst_vars (Lazy.force model) (Spec.ivars spec)
                  Term.(cspec && cconn && clib)
              in
              Solver.add ~solver (Term.magic csynth) ;
              loop (n + 1) )
  in
  loop 1

let%expect_test "" =
  let lib = [Component.add 0; Component.one 1] in
  let spec =
    Spec.
      { inputs= [Type.(Wrapped.wrap Int)]
      ; output= Type.(Wrapped.wrap Int)
      ; constr=
          (fun ins out ->
            match ins with [x] -> Term.(magic x < magic out) | _ -> assert false) }
  in
  solve 10 lib spec |> Or_error.ok_exn |> Program.to_string |> print_endline;
  [%expect {|
    x0 = one
    x1 = add i0 x0 |}]

let%expect_test "" =
  let lib = [Component.add 0; Component.one 1] in
  let spec =
    Spec.
      { inputs= [Type.(Wrapped.wrap Int)]
      ; output= Type.(Wrapped.wrap Int)
      ; constr=
          (fun ins out ->
            match ins with
            | [x] -> Term.(magic x * int 2 = magic out)
            | _ -> assert false) }
  in
  solve 10 lib spec |> Or_error.ok_exn |> Program.to_string |> print_endline;
  [%expect {|
    x0 = one
    x1 = add i0 i0 |}]
