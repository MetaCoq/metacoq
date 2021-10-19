
let rec read_line chan accu = match input_line chan with
| l -> read_line chan (l :: accu)
| exception End_of_file ->
  List.rev accu

let read_file f =
  let chan = open_in f in
  let ans = read_line chan [] in
  let () = close_in chan in
  ans

let parse_log line =
  let line = String.split_on_char ' ' line in
  match line with
  | "File" :: f :: "line" :: n :: "characters" :: c :: _ ->
    let f = String.sub f 1 (String.length f - 3) in
    (* let f = String.sub f 20 (String.length f - 20) in *)
    let n = int_of_string @@ String.sub n 0 (String.length n - 1) in
    let chars = String.split_on_char '-' c in
    (match chars with
    | "0" :: _ -> Some (f, n)
    | _ -> None)
  | _ -> None

let rec parse_logs = function
| [] -> []
| l :: lines ->
  match parse_log l with
  | None -> parse_logs lines
  | Some l -> l :: parse_logs lines

module StringMap = Map.Make(String)

let fwd (pre, suf) = match suf with
| [] -> None
| x :: suf -> Some (x :: pre, suf)

let bwd (pre, suf) = match pre with
| [] -> None
| x :: pre -> Some (pre, x :: suf)

let rec goto n zip =
  if n <= 0 then zip
  else match fwd zip with
  | None -> zip
  | Some zip -> goto (n - 1) zip

let is_instance l =
  let check = function "Instance" | "Rewrite" -> true | _ -> false in
  List.exists check (String.split_on_char ' ' l)

let rec match_instance n ((pre, suf) as zip) =
  if n = 0 then None
  else match suf with
  | [] -> None
  | x :: suf ->
  if is_instance x then Some (pre, "#[global]" :: x :: suf)
  else match bwd zip with
  | None -> None
  | Some zip -> match_instance (n - 1) zip

let handle_file f todo =
  let max_diff = 20 in
  let lines = read_file f in
  let todo = List.sort (Pervasives.compare : int -> int -> int) todo in
  let fold (off, accu) n =
    let zip = goto (off + n) ([], accu) in
    match match_instance max_diff zip with
    | None -> (off, accu)
    | Some (pre, suf) ->
      let accu = List.rev_append pre suf in
      (off + 1, accu)
  in
  let _, lines = List.fold_left fold (0, lines) todo in
  let chan = open_out f in
  let iter l =
    output_string chan l;
    output_char chan '\n'
  in
  let () = List.iter iter lines in
  close_out chan

let () =
  let file = Sys.argv.(1) in
  let lines = read_file file in
  let log = parse_logs lines in
  let fold accu (f, n) =
    let l = try StringMap.find f accu with Not_found -> [] in
    StringMap.add f (n :: l) accu
  in
  let log = List.fold_left fold StringMap.empty log in
  StringMap.iter handle_file log
