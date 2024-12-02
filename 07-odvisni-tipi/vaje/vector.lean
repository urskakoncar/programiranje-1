-- Vzamemo stvari iz predavanj
set_option autoImplicit false

inductive Naravno : Type where
  | nic : Naravno
  | naslednik : Naravno → Naravno
deriving Repr


def plus : Naravno → Naravno → Naravno :=
  fun m n =>
    match m with
    | Naravno.nic => n
    | Naravno.naslednik m' =>
        Naravno.naslednik (plus m' n)

-- Vektorji

inductive Vektor : Type → Naravno → Type where
  | prazen : {A : Type} → Vektor A Naravno.nic
  | sestavljen : {A : Type} → {n : Naravno} → A → Vektor A n → Vektor A (Naravno.naslednik n)
deriving Repr

#check (Vektor.sestavljen "a" (Vektor.sestavljen "b" (Vektor.prazen)))

def stakni_vektorja : {A : Type} → {m n : Naravno} → Vektor A m → Vektor A n → Vektor A (plus m n) :=
  fun {A : Type} {m n : Naravno} (xs : Vektor A m) (ys : Vektor A n) =>
    match xs with
    | Vektor.prazen => ys
    | Vektor.sestavljen x xs' => Vektor.sestavljen x (stakni_vektorja xs' ys)


-- Sedaj lahko definiramo `lookup`, ki ne bo nikoli povzročil napake.
inductive Finite : Naravno -> Type where -- slika iz natavnih štrvil v tip;
-- lahko si ga predstavlljamo kot naravna st omejena z nekim n; [0, 1, ... , n)
  | fzero : {n : Naravno} -> Finite (Naravno.naslednik n) -- ta nam da [0, 1, ---, n, n + 1]
  | fsucc : {n : Naravno} -> Finite n -> Finite (Naravno.naslednik n) -- gradimo intervale ?


def lookup {A : Type} {n : Naravno} : Vektor A n -> Finite n -> A :=
  fun xs i =>
    match i, xs with -- i tipa Finite, ima dva konstruktorja
    | Finite.fzero, Vektor.sestavljen y ys => y
    | Finite.fsucc i', Vektor.sestavljen y ys => lookup ys i'


-- Včasih enakost tipov ni takoj očitna in jo moramo izpeljati
-- Dopolnite naslednjo definicijo, vse potrebne leme pa dokažite kar s taktiko `sorry`.

def plus_zero (n : Naravno) : (plus n Naravno.nic) = n := by
  sorry

def plus_add_suc (m n : Naravno) : (plus m (Naravno.naslednik n)) = (Naravno.naslednik (plus m n)) := by
  sorry

def plus_comm (m n : Naravno) : (plus m n) = (plus n m) := by
  sorry

-- xs ys
-- xs @ ys : Vector A (n + m)
-- xs @ ys : Vector A (m + n)
def stakni_vektorja' : {A : Type} → {m n : Naravno} → Vektor A m → Vektor A n → Vektor A (plus n m) :=
 fun {A : Type} {m n : Naravno} (xs : Vektor A m) (ys : Vektor A n) =>
  match xs with
    | Vektor.prazen =>
      by
        rw [plus_zero]
        exact ys
    | Vektor.sestavljen x xs' =>
      by
        have aux := Vektor.sestavljen x (stakni_vektorja xs' ys)
        rw [plus_add_suc, plus_comm]
        exact aux

-- DN!!!!!, neka komutativnost ??



--ustvarimo lemo za pomoč pri naslednji nalogi: dn dokaži
def add_c : {m n : Naravno} -> plus m n = plus n m := sorry

-- Uporabite samo definicijo `stakni_vektorja'` in taktike `rw` in `exact`.
def stakni_vektorja'' : {A : Type} → {m n : Naravno} → Vektor A m → Vektor A n → Vektor A (plus m n) :=
  by
    intro A m n xs ys
    have xx := stakni_vektorja' xs ys
    rw [add_c] -- lahko tudi dodamo se: at xx
    exact xx
