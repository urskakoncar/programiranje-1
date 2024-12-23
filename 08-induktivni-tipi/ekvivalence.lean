def concat {A : Type} : List A → List A → List A :=
  fun xs ys =>
    match xs with
    | [] => ys
    | x :: xs' => x :: concat xs' ys

#check (concat ["a", "b"] ["c", "d"])

def reverse {A : Type} : List A → List A :=
  fun xs =>
    match xs with
    | [] => xs
    | x :: xs' => concat (reverse xs') [x]


#eval (reverse ["a", "b", "c", "d"])

def length {A : Type} : List A → Nat :=
  fun xs =>
    match xs with
    | [] => 0
    | x :: xs' => 1 + length xs'


#eval (length ["a", "b", "c", "d"])

theorem trd1  {A : Type} {x : A} : reverse [x] = [x] :=
  by
    simp [reverse]
    simp [concat]
    --simp uporabi podano funkcijo kjerkoli jo zna uporabit, gre le v eno smer

theorem trd2 {A : Type} {xs ys : List A} : length (concat xs ys) = length xs + length ys :=
  by
    induction xs with
    | nil => simp [concat, length]
    | cons x xs' ip =>
      simp [concat, length]
      rw [ip, Nat.add_assoc]

-- Tega poznamo že iz predavanj
theorem trd3 {A : Type} {xs : List A} : concat xs [] = xs :=
  by
    induction xs with
    | nil =>
      simp [concat]
    | cons x xs' ih =>
      simp [concat]
      rw [ih]

theorem trd4 {A : Type} {xs ys zs : List A} : concat (concat xs ys) zs = concat xs (concat ys zs) :=
  by
    induction xs with
    | nil =>
      simp [concat]
    | cons x xs' ip =>
      simp [concat]
      rw [ip]
      --namesto rw [ip] bi lahko napisala samo exact ip


theorem trd5 {A : Type} {xs ys : List A} : reverse (concat xs ys) = concat (reverse ys) (reverse xs) :=
  by
    induction xs with
    | nil =>
      simp [reverse, concat]
      rw [trd3]
    | cons x xs' ip =>
      simp [reverse, concat, reverse]
      rw [ip]
      rw [trd4]



theorem trd6 {A : Type} {xs : List A} : length (reverse xs) = length xs :=
  by
    induction xs with
    | nil => simp [reverse]
    | cons x xs' ip =>
      simp [reverse, length, concat, trd2]
      rw [ip, Nat.add_comm]


theorem trd7 {A : Type} {xs : List A} : reverse (reverse xs) = xs :=
  by
    induction xs with
    | nil => simp [reverse]
    | cons x xs' ip =>
      simp [reverse, concat, reverse, trd5]
      exact ip

def map {A B : Type} : (A → B) → List A → List B :=
  fun f xs =>
    match xs with
    | [] => []
    | x :: xs' => f x :: map f xs'

theorem map_assoc {A B C : Type} {f : A → B} {g : B → C} {xs : List A} : map g (map f xs) = map (g ∘ f) xs :=
  by
    induction xs with
    | nil =>
      simp [map]
    | cons x xs' ip =>
      simp [map, ip]


theorem map_id {A : Type} {xs : List A} : map id xs = xs :=
  by
    induction xs with
    | nil =>
      simp [map, map_assoc]
    | cons x xs' ip =>
      simp [map, ip]


theorem map_concat {A B : Type} {f : A → B} {xs ys : List A} : map f (concat xs ys) = concat (map f xs) (map f ys) :=
  by
    induction xs with
    | nil =>
      simp [concat]
    | cons x xs' ip =>
      simp [concat, map, ip]


theorem map_reverse {A B : Type} {f : A → B} {xs : List A} : map f (reverse xs) = reverse (map f xs) :=
  by
    induction xs with
    | nil =>
      simp [map, reverse]
    | cons x xs' ip =>
      simp [map, concat, reverse, map_concat]
      rw [ip]


-- DREVESA !!!!!!!!!!!! %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
inductive tree (A : Type) : Type where
  | empty : tree A
  | node : A → tree A → tree A → tree A

#check tree.rec

def tree_map {A B : Type} : (A → B) → tree A → tree B :=
  fun f drevo =>
    match drevo with
    | tree.empty => tree.empty
    | tree.node x levi desni => tree.node (f x) (tree_map f levi) (tree_map f desni)


theorem tree_map_empty {A B : Type} {f : A → B} : tree_map f tree.empty = tree.empty :=
  by
    simp [tree_map]

theorem tree_map_comp {A B C : Type} {f : A → B} {g : B → C} {t : tree A} : tree_map g (tree_map f t) = tree_map (g ∘ f) t :=
  by
    induction t with
    | empty =>
      simp [tree_map]
    | node x l d ipl ipr =>
      simp [tree_map, ipl, ipr]

def depth {A : Type} : tree A → Nat :=
  fun t =>
    match t with
    | tree.empty => 0
    | tree.node _ l r => 1 + Nat.max (depth l) (depth r)


-- S tem se ne bomo ukvarjali
theorem max_comm {a b : Nat} : Nat.max a b = Nat.max b a :=
  sorry

def mirror {A : Type} : tree A → tree A :=
  fun t =>
    match t with
    | tree.empty => tree.empty
    | tree.node x levi desni => tree.node x (mirror desni) (mirror levi)

theorem mirror_depth {A : Type} {t : tree A} : depth (mirror t) = depth t :=
  by
    induction t with
    | empty =>
      simp [depth]
    | node x l r ip_l ip_r =>
      simp [mirror, depth]
      rw [ip_l, ip_r]
      rw [max_comm]

theorem mirror_mirror {A : Type} {t : tree A} : mirror (mirror t) = t :=
  by
    induction t with
    | empty =>
      simp [mirror]
    | node x l d ihl ihd =>
      simp [mirror, ihl, ihd]


def collect {A : Type} : tree A → List A :=
  fun t =>
    match t with
    | tree.empty => []
    | tree.node x l r => concat (collect l) (concat [x]  (collect r))

theorem trd8 {A : Type} {x : A} {xs ys : List A} : concat xs (x::ys) = concat (concat xs [x]) ys :=
  by
    induction xs with
    | nil =>
      simp [concat]
    | cons x xs' ih =>
      simp [concat]
      rw [ih]


theorem collect_mirror {A : Type} {t : tree A} : collect (mirror t) = reverse (collect t) :=
  by
    induction t with
    | empty =>
      simp [collect, reverse]
    | node x l r ihl ihr =>
      simp [mirror, collect, reverse]
      rw [ihl, ihr]
      simp [concat]
      rw [trd5, trd8]
      simp [reverse]


def size {A : Type} : tree A → Nat :=
  fun t =>
    match t with
    | tree.empty => 0
    | tree.node _ l r => 1 + size l + size r


theorem size_mirror {A : Type} {t : tree A} : size (mirror t) = size t :=
  by
    induction t with
    | empty =>
      simp [size]
    | node x l r ihl ihr =>
      simp [mirror, size, ihr, ihl]
      simp [Nat.add_assoc, Nat.add_comm (size r) (size l)]


--- Indukcija na pomožnih funkcijah z akumulatorjem

theorem concat2 : concat xs (x :: ys) = concat (concat (xs) [x]) ys :=
  by
    induction xs with
    | nil => simp [concat]
    | cons x' xs' ih =>
      simp [concat]
      assumption

-- Definirajte repno rekurzivno funkcijo, ki obrne seznam
def reverse' {A : Type} (xs: List A) : List A :=
  let rec aux : List A -> List A -> List A
    | [], acc => acc
    | x' :: xs', acc => aux xs' (x' :: acc)
  aux xs []


def reverse'' {A : Type} : List A -> List A :=
  fun xs =>
    match xs with
    | [] => []
    | x :: xs' => (reverse'' xs') ++ [x]


-- Dokažite, da je vaša funkcija pravilna
theorem reverse''_eq_reverse'.aux {A : Type} :
∀ {xs acc : List A},
(reverse'' xs) ++ acc = reverse'.aux xs acc :=
  by
    intro xs
    induction xs with
    | nil =>
      simp [reverse'', reverse'.aux]
    | cons x xs' ih =>
      intro acc
      simp [reverse'', reverse'.aux]
      rw [ih]


theorem reverse''_eq_reverse' {A : Type} :
∀ {xs : List A}, reverse'' xs = reverse' xs :=
  by
    intro xs
    induction xs with
    | nil =>
      simp [reverse'', reverse', reverse'.aux]
    | cons x xs' ih =>
      simp [reverse', reverse'', reverse'.aux]
      exact reverse''_eq_reverse'.aux


theorem reverse_eq_reverse'.aux {A : Type} :
∀ {xs acc : List A},
concat (reverse xs) acc = reverse'.aux xs acc :=
  by
    intro xs
    induction xs with
    | nil =>
      simp [reverse, reverse'.aux, concat]
    | cons x xs' ih =>
      intro acc
      simp [reverse, reverse'.aux, concat]
      rw [← concat2]
      rw [ih]


theorem reverse_eq_reverse' {A : Type} :
∀ {xs : List A}, reverse xs = reverse' xs :=
  by
    sorry
