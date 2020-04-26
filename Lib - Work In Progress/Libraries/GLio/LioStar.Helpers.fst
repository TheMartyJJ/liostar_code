module LioStar.Helpers

module F = FStar.FunctionalExtensionality
module L = FStar.List.Tot

let rec map_with_state_lowStar (f: 'a -> 'b -> 'c) (v: 'a) (l: list 'b)
  : list 'c
  = match l with
  | []    -> []
  | hd::tl -> f v hd :: map_with_state_lowStar f v tl

let map_with_state_native (f: 'a -> 'b -> 'c) (v: 'a) (l: list 'b)
  = L.map (f v) l

// let ondom3 (f: 'a -> 'b -> 'c -> 'd)
//   : F.arrow 'a (fun _ -> F.arrow 'b (fun _ -> F.arrow 'c (fun _ -> 'd))) =
//   fun a b c -> F.on_domain 'c (F.on_domain 'b (F.on_domain 'a f a) b) c

// let map_with_state_lowStar' = ondom3 map_with_state_lowStar
// let map_with_state_native' = ondom3 map_with_state_native

// let rec lemma_map_with_state_map f v l
//   : Lemma (map_with_state_native' f v l == map_with_state_lowStar' f v l)
//     [SMTPat (map_with_state_native' f v l)]
//   = match l with
//   | [] -> ()
//   | hd::tl -> lemma_map_with_state_map f v tl

let map_with_state = map_with_state_lowStar

let rec filter_with_state_lowStar (f: 'a -> 'b -> bool) (v: 'a) (l: list 'b)
  : list 'b
  = match l with
  | []    -> []
  | hd::tl -> if f v hd
            then hd::filter_with_state_lowStar f v tl
            else    filter_with_state_lowStar f v tl

let filter_with_state = filter_with_state_lowStar

