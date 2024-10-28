(*----------------------------------------------------------------------------*
 # Rekurzija
[*----------------------------------------------------------------------------*)

let rec reverse1 sez =
  match sez with
    | [] -> []
    | h :: t -> reverse1 t @ [h]


(*če želimo repno rekurzivno funcijo:*)
let reverse_boljsi sez =
  let rec reverse1 kup_za_obrnit na_zacetku_prazen_kup =
    match kup_za_obrnit with
      | [] -> na_zacetku_prazen_kup
      | h :: t -> reverse1 t (h :: na_zacetku_prazen_kup)
  in reverse1 sez []

let rec sum l = match l with
  | [] -> 0
  | x::xs -> (sum xs) + x


let rec sum_better l = 
  let rec sum2 l acc = match l with
    | [] -> acc
    | x::xs -> sum2 xs (acc + x)
  in
  sum2 l 0



(*----------------------------------------------------------------------------*]
 Funkcija [repeat x n] vrne seznam [n] ponovitev vrednosti [x]. Za neprimerne
 vrednosti [n] funkcija vrne prazen seznam.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # repeat "A" 5;;
 - : string list = ["A"; "A"; "A"; "A"; "A"]
 # repeat "A" (-2);;
 - : string list = []
[*----------------------------------------------------------------------------*)

let rec repeat x n = 
  match n with
    | 0 -> []
    | n -> if n <= 0 then [] else [x] @ repeat x (n - 1)

(*----------------------------------------------------------------------------*]
 Funkcija [range] sprejme število in vrne seznam vseh celih števil od 0 do
 vključno danega števila. Za neprimerne argumente funkcija vrne prazen seznam.
 Funkcija je repno rekurzivna.
Pri tem ne smete uporabiti vgrajene funkcije [List.init].
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # range 10;;
 - : int list = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
[*----------------------------------------------------------------------------*)

let rec range n =
  match n with
    | 0 -> [0]
    | _ -> if n < 0 then [] else range (n - 1) @ [n]
    (*to ni repno rekurzivna funkcija*)

let range n = 
  let rec range_pomozna n sez =
    match n with
      | 0 -> 0 :: sez
      | _ -> if n < 0 then [] else range_pomozna (n - 1) (n :: sez)
  in
  range_pomozna n []


(*----------------------------------------------------------------------------*]
 Funkcija [map f list] sprejme seznam [list] oblike [x0; x1; x2; ...] in
 funkcijo [f] ter vrne seznam preslikanih vrednosti, torej
 [f x0; f x1; f x2; ...].
 Pri tem ne smete uporabiti vgrajene funkcije [List.map].
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # let plus_two = (+) 2 in
   map plus_two [0; 1; 2; 3; 4];;
 - : int list = [2; 3; 4; 5; 6]
[*----------------------------------------------------------------------------*)

let rec map f sez =
  match sez with
    | [] -> []
    | x::xs -> f x :: map f xs 

(*----------------------------------------------------------------------------*
 ## Funkcija `repeat`
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Funkcija `repeat x n` vrne seznam `n` ponovitev vrednosti `x`. Za neprimerne
  vrednosti `n` funkcija vrne prazen seznam.
[*----------------------------------------------------------------------------*)

let rec map_tlrec f sez = 
  let rec map_tlrec_pomozna f sez nov=
    match sez with
      | [] -> nov
      | x::xs -> map_tlrec_pomozna f xs (nov @ [f x])
  in
  map_tlrec_pomozna f sez []

let primer_repeat_1 = repeat "A" 5
(* val primer_repeat_1 : string list = ["A"; "A"; "A"; "A"; "A"] *)

let primer_repeat_2 = repeat "A" (-2)
(* val primer_repeat_2 : string list = [] *)

(*----------------------------------------------------------------------------*
 ## Funkcija `range`
[*----------------------------------------------------------------------------*)
let rec mapi f sez =
  let rec mapi_pomozna f sez i nov =
    match sez with
      | [] -> nov
      | x::xs -> mapi_pomozna f xs (i + 1) (nov @ [f x i])
  in
  mapi_pomozna f sez 0 []

(*----------------------------------------------------------------------------*]
 Funkcija [zip] sprejme dva seznama in vrne seznam parov istoležnih
 elementov podanih seznamov. Če seznama nista enake dolžine vrne napako.
 Pri tem ne smete uporabiti vgrajene funkcije [List.combine].
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # zip [1; 1; 1; 1] [0; 1; 2; 3];;
 - : (int * int) list = [(1, 0); (1, 1); (1, 2); (1, 3)]
 # zip [1; 1; 1; 1] [1; 2; 3; 4; 5];;
 Exception: Failure "Different lengths of input lists.".
[*----------------------------------------------------------------------------*)
let res dolzina_seznama sez =
  let rec dolzina_seznama_pomozna sez n=
    match sez with
      | [] -> n
      | x::xs -> dolzina_seznama_pomozna xs (n + 1)
  in
  dolzina_seznama_pomozna sez 0


let rec zip sez1 sez2 =   
  let rec zip_pomozna sez1 sez2 nov = 
    match sez1, sez2 with
      | [], [] -> nov
      | _, [] -> failwith "Different lengths of input lists."
      | [], _ -> failwith "Different lengths of input lists."
      | x::xs, y::ys -> zip_pomozna xs ys (nov @ [(x, y)])
  in
  zip_pomozna sez1 sez2 []

(*drug nacin*)
let rec zip_1 sez1 sez2 =
  match sez1, sez2 with
  | [], [] -> []
  | _, [] | [], _ -> failwith "Different lengths of input lists."
  | x :: xs, y :: ys -> (x, y) :: (zip_1 xs ys)


let primer_range = range 10
(* val primer_range : int list = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10] *)

(*----------------------------------------------------------------------------*
 ## Funkcija `map`
[*----------------------------------------------------------------------------*)

let rec unzip sez = 
  let rec unzip_pomozna sez nov1 nov2 =
    match sez with
    |[] -> (nov1, nov2)
    |(a, b)::xs -> unzip_pomozna xs (nov1 @ [a]) (nov2 @ [b])
  in
  unzip_pomozna sez [] []

(*----------------------------------------------------------------------------*]
 Funkcija [unzip_tlrec] je repno rekurzivna različica funkcije [unzip].
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # unzip_tlrec [(0,"a"); (1,"b"); (2,"c")];;
 - : int list * string list = ([0; 1; 2], ["a"; "b"; "c"])
[*----------------------------------------------------------------------------*)

let rec map _ _ = ()

let primer_map_1 =
  let plus_two = (+) 2 in
  map plus_two [0; 1; 2; 3; 4]
(* val primer_map_1 : int list = [2; 3; 4; 5; 6] *)

(*----------------------------------------------------------------------------*
 Napišite še funkcijo `map_tlrec`, ki naj bo repno rekurzivna različica funkcije
 `map`.
[*----------------------------------------------------------------------------*)

let rec loop condition f x =
  if condition x then loop condition f (f x) else x


let primer_map_2 =
  let plus_two = (+) 2 in
  map_tlrec plus_two [0; 1; 2; 3; 4]
(* val primer_map_2 : int list = [2; 3; 4; 5; 6] *)

(*----------------------------------------------------------------------------*
 ## Funkcija `mapi`
[*----------------------------------------------------------------------------*)

let rec fold_left_no_acc f sez =
  match sez with
  | [] | _ :: [] -> failwith "prekratek seznam"
  | x :: y :: [] -> f x y
  | x :: y :: t -> fold_left_no_acc f ( (f x y) :: t)
(*???????????*)

 ```python
 def mapi(f, lst):
     mapi_lst = []
     index = 0
     for x in lst:
         mapi_lst.append(f(index, x))
         index += 1
     return mapi_lst
 ```

 Pri tem ne smete uporabiti vgrajene funkcije `List.mapi`.
[*----------------------------------------------------------------------------*)

let rec apply_sequence f x n = 
  if n < 0 then [] else x :: apply_sequence f (f x) (n - 1)

let rec apply_sequence f x n =
  let rec pomozna f x n nov =
    if n < 0
      then nov
    else 
      pomozna f (f x) (n - 1) (nov @ [x])
  in
  pomozna f x n []


let primer_mapi = mapi (+) [0; 0; 0; 2; 2; 2]
(* val primer_mapi : int list = [0; 1; 2; 5; 6; 7] *)

(*----------------------------------------------------------------------------*
 ## Funkcija `zip`
[*----------------------------------------------------------------------------*)

let rec filter f list =
  match list with
  | [] -> []
  | x::xs -> if f x then x :: (filter f xs) else filter f xs 

(*----------------------------------------------------------------------------*]
 Funkcija [exists] sprejme seznam in funkcijo, ter vrne vrednost [true] čim
 obstaja element seznama, za katerega funkcija vrne [true] in [false] sicer.
 Funkcija je repno rekurzivna.
 Pri tem ne smete uporabiti vgrajene funkcije [List.find] ali podobnih.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # exists ((<) 3) [0; 1; 2; 3; 4; 5];;
 - : bool = true
 # exists ((<) 8) [0; 1; 2; 3; 4; 5];;
 - : bool = false
[*----------------------------------------------------------------------------*)

let rec exists f sez = 
  match sez with
  | [] -> false
  | x :: xs -> if f x then true else exists f xs

(*----------------------------------------------------------------------------*]
 Funkcija [first f default list] vrne prvi element seznama, za katerega
 funkcija [f] vrne [true]. Če takšnega elementa ni, vrne [default].
 Funkcija je repno rekurzivna.
 Pri tem ne smete uporabiti vgrajene funkcije [List.find] ali podobnih. 
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # first ((<) 3) 0 [1; 1; 2; 3; 5; 8];;
 - : int = 5
 # s
 - : int = 0
[*----------------------------------------------------------------------------*)

let rec first f default list = 
  match list with
  | [] -> default
  | x :: xs -> if f x then x else first f default xs
