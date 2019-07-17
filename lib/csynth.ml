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
    ; constr: zany Term.t list -> zany Term.t -> zbool Term.t }

  let name {name; id; _} = sprintf "%s_%d" name id

  let ivar c i n =
    let t = List.nth_exn c.inputs i in
    let name = sprintf "%s_in%d_%d" (name c) i n in
    Type.Wrapped.unwrap {run= (fun t -> Symbol.declare t name |> Term.symbol)} t

  let ovar c n =
    let name = sprintf "%s_out_%d" (name c) n in
    Type.Wrapped.unwrap
      {run= (fun t -> Symbol.declare t name |> Term.symbol)}
      c.output

  let constr cs n =
    List.map cs ~f:(fun c ->
        c.constr
          (List.init (List.length c.inputs) ~f:(fun i -> ivar c i n))
          (ovar c n))
    |> Term.and_

  let iloc c i = Symbol.declare Int (sprintf "l_%s_in%d" (name c) i) |> Term.symbol

  let oloc c = Symbol.declare Int (sprintf "l_%s_out" (name c)) |> Term.symbol

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
    ; constr= (fun _ out -> Term.(int 1 = out)) }
end

module Program = struct
  type t = (Component.t * [`Input of int | `Var of int] list) list
end

module Spec = struct
  type t =
    { inputs: Type.Wrapped.t list
    ; output: Type.Wrapped.t
    ; constr: zany Term.t list -> zany Term.t -> zbool Term.t }

  let ivar c i =
    let t = List.nth_exn c.inputs i in
    let name = sprintf "in%d" i in
    Type.Wrapped.unwrap {run= (fun t -> Symbol.declare t name |> Term.symbol)} t

  let ovar c n =
    let name = sprintf "out_%d" n in
    Type.Wrapped.unwrap
      {run= (fun t -> Symbol.declare t name |> Term.symbol)}
      c.output

  let constr c n =
    c.constr (List.init (List.length c.inputs) ~f:(ivar c)) (ovar c n)

  let iloc i = Symbol.declare Int (sprintf "l_in%d" i) |> Term.symbol

  let oloc m = Term.int (m - 1)
end

(** Generate a well-formedness constraint. This constraint combines the
   consistency, acyclicity, and location range constraints. This constraint only
   refers to the location variables. *)
let well_formed lib spec =
  let open Component in
  let consistent = Term.distinct (List.map lib ~f:oloc) in
  let acyclic =
    List.concat_map lib ~f:(fun c ->
        List.init (List.length c.inputs) ~f:(fun i -> Term.(iloc c i < oloc c)))
    |> Term.and_
  in
  let nlines = List.length lib + List.length spec.Spec.inputs in
  (* Parameters can refer to any input and any intermediate value. *)
  let param_range =
    Term.(
      List.concat_map lib ~f:(fun c ->
          List.init (List.length c.inputs) ~f:(fun i ->
              int 0 <= iloc c i && iloc c i < int nlines))
      |> and_)
  in
  (* Outputs can only be intermediate values. *)
  let ret_range =
    Term.(
      List.map lib ~f:(fun c ->
          int (List.length spec.inputs) <= oloc c && oloc c < int nlines)
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
            (oloc c, ovar c n)
            :: List.init (List.length c.inputs) ~f:(fun i -> (iloc c i, ivar c n i))))
  in
  List.concat_map pairs ~f:(fun (l1, t1) ->
      List.map pairs ~f:(fun (l2, t2) -> Term.(l1 = l2 ==> (t1 = t2))))
  |> Term.and_

let solve lib spec =
  let solver = Solver.make () in
  let well_formed_constr = well_formed lib spec in
  Solver.add ~solver well_formed_constr ;
  let verifier = Solver.make () in
  Solver.add ~solver:verifier (Component.constr lib 0) ;
  Solver.add ~solver:verifier Term.(not (Spec.constr spec 0)) ;
  let conn_constr = connection 0 lib spec in
  let rec loop n =
    match Solver.(check ~solver []) with
    | Unsat proof ->
        Or_error.errorf "Synthesis failed: %s" (Term.to_string (Lazy.force proof))
    | Unknown e -> Or_error.errorf "Synthesis failed: %s" e
    | Sat model -> (
        let conn_constr = Model.eval ~model:(Lazy.force model) conn_constr in
        match Solver.(check ~solver:verifier [conn_constr]) with
        | Unsat _ -> Ok ()
        | Unknown e -> Or_error.errorf "Synthesis failed: %s" e
        | Sat model ->
            let cspec = Spec.constr spec n in
            let cconn = connection n lib spec in
            let clib = Component.constr lib n in
            eprintf "%s\n" (Term.to_string Term.(cspec && cconn && clib)) ;
            eprintf "%s\n" (Model.to_string (Lazy.force model)) ;
            let csynth =
              Model.eval ~model:(Lazy.force model) Term.(cspec && cconn && clib)
            in
            eprintf "%s\n" (Term.to_string csynth) ;
            Solver.add ~solver csynth ;
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
  solve lib spec |> Or_error.ok_exn
