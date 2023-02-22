{-# OPTIONS --cubical #-}
module Library where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
open import Agda.Primitive

-- Sometimes the type signature matters.
infixl 14 ⟨_⟩_
⟨_⟩_ : ∀{l} (A : Set l) → A → A
⟨ T ⟩ t = t

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

absurd : ∀{l} {A : Set l} → ⊥ → A
absurd ()

data Bool : Set where
  false true : Bool

true≢false : true ≡ false → ⊥
true≢false true≡false = transport (cong (λ{true → ⊤; false → ⊥}) true≡false) tt

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

id : {A : Set} → A → A
id x = x

const : ∀{m l} {A : Set m} {B : Set l} → A → B → A
const x y = x

pcong : {A B : Set} → {x y : A} → {f g : A → B} → (f ≡ g) → (f x ≡ f y) → (g x ≡ g y)
pcong {x = x} {y = y} f≡g = transp (λ i → f≡g i x ≡ f≡g i y) i0

dcong : ∀{l m} {A : I → Set m} {B : (i : I) → A i → Set l}
     → (f : {i : I} → (a : A i) → B i a) {x : A i0} {y : A i1}
     → (p : PathP A x y) → PathP (λ i → B i (p i)) (f {i0} x) (f {i1} y)
dcong f p i = f {i} (p i)

dcong₂ : ∀{l m n} {A : I → Set m} {B : (i : I) → A i → Set l} {C : (i : I) → (x : A i) → B i x → Set n}
      → (f : {i : I} → (a : A i) → (b : B i a) → C i a b) {x : A i0} {y : A i1} {z : B i0 x} {w : B i1 y}
      → (p : PathP A x y) → (q : PathP (λ i → B i (p i)) z w)
      → PathP (λ i → C i (p i) (q i)) (f {i0} x z) (f {i1} y w)
dcong₂ f p q i = f {i} (p i) (q i)

sym : ∀ {l} {P : I → Type l} {x : P i0} {y : P i1} → PathP P x y → PathP (λ i → P (~ i)) y x
sym Pxy i = Pxy (~ i)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

just-injective : {B : I → Set} {a : B i0} {b : B i1} → PathP (λ i → Maybe (B i)) (just a) (just b) → PathP B a b
just-injective {B} ja≡jb i = just-elim (ja≡jb i) (λ j → ja≡jb (i ∧ j))
  where just-elim : {x : B i0} (z : Maybe (B i)) → PathP (λ j → Maybe (B (i ∧ j))) (just x) z → B i
        just-elim (just z) _ = z
        just-elim nothing jx≡z = absurd (transport (dcong (λ{(just _) → ⊤; nothing → ⊥}) jx≡z) tt)

data Decidable (A : Set) : Set where
  yes : A → Decidable A
  no : (A → ⊥) → Decidable A

Discrete : Set → Set
Discrete X = (x y : X) → Decidable (x ≡ y)

Constant : {X Y : Set} → (X → Y) → Set
Constant {X} f = (x y : X) → f x ≡ f y

Collapsible : Set → Set
Collapsible X = Σ[ f ∈ (X → X) ] Constant f

PathCollapsible : Set → Set
PathCollapsible X = (x y : X) → Collapsible (x ≡ y)

discreteToPathCollapsible : {X : Set}
                          → Discrete X → PathCollapsible X
discreteToPathCollapsible {X} d x y
  = map , cm
  where map : x ≡ y → x ≡ y
        map x≡y with d x y
        map x≡y | yes x≡y' = x≡y'
        map x≡y | no f = absurd (f x≡y)
        cm : Constant map
        cm p q with d x y
        cm p q | yes x = (λ i → x)
        cm p q | no x = absurd (x p)

pathCollapsibleToisSet : {X : Set}
                       → PathCollapsible X → isSet X
pathCollapsibleToisSet {X} pc x y p q = pcong lif (cong g (snd (pc x y) p q))
   where g : x ≡ y → x ≡ y
         g x≡y = x≡y ∙ sym (fst (pc y y) refl)
         lif : g ∘ (fst (pc x y)) ≡ id
         lif i x≡y = J (λ y x≡y → fst (pc x y) x≡y ∙ sym (fst (pc y y) refl) ≡ x≡y)
                       (rCancel (fst (pc x x) refl))
                       x≡y i

-- Hedberg's theorem
discreteToisSet : {X : Set} → Discrete X → isSet X
discreteToisSet d = pathCollapsibleToisSet (discreteToPathCollapsible d)

Stable : Set → Set
Stable X = ((X → ⊥) → ⊥) → X

Separated : Set → Set
Separated X = (x y : X) → Stable (x ≡ y)

separatedToisSet : {X : Set} → Separated X → isSet X
separatedToisSet {X} sep = pathCollapsibleToisSet λ x y → (sep x y ∘ obvious x y) , c x y
  where obvious : (x y : X) → (x ≡ y) → ((x ≡ y → ⊥) → ⊥)
        obvious x y x≡y f = f x≡y
        lemma : {X : Set} (p q : X → ⊥) → (x : X) → p x ≡ q x
        lemma p q x = absurd (p x)
        lemma₂ : {X : Set} (p q : X → ⊥) → p ≡ q
        lemma₂ p q i x = lemma p q x i
        c : (x y : X) → Constant (sep x y ∘ obvious x y)
        c x y x≡y₁ x≡y₂ i j = sep x y (lemma₂ (obvious x y x≡y₁) (obvious x y x≡y₂) i) j

congPreservesConstant : {A B : Set} → {f : A → B} {x y : A}
                       → Constant f → Constant (cong {x = x} {y = y} f)
congPreservesConstant {f = f} {x = x} {y = y} cf p q = lemma p ∙ sym (lemma q)
  where lemma : ∀ p → cong {x = x} {y = y} f p ≡ sym (cf x x) ∙ cf x y
        lemma = J (λ y x≡y → cong {x = x} {y = y} f x≡y ≡ sym (cf x x) ∙ cf x y)
                  (sym (lCancel (cf x x)))

isSetPath : ∀ {l} {B : I → Set l}
          → ((i : I) → isSet (B i))
          → {x : B i0} → {y : B i1} → (p q : PathP B x y)
          → p ≡ q
isSetPath {B = B} H {x} {y} p q i j = comp (λ k → B (~ k ∨ j))
                                            (λ k → λ{(i = i0) → side-square p (~ j) (~ k)
                                                     ;(i = i1) → side-square q (~ j) (~ k)
                                                     ;(j = i0) → t (~ k)
                                                     ;(j = i1) → y})
                                            (H i1 _ y
                                               (λ k → side-edge p (~ k))
                                               (λ k → side-edge q (~ k))
                                               i j)
  where t : (i : I) → B i
        t = fill B {i0} (λ k ()) (inS x)
        side-square : PathP B x y → (i j : I) → B (~ i ∨ j)
        side-square r i = fill (λ j → B (~ i ∨ j))
                               (λ j → λ{(i = i0) → y
                                        ;(i = i1) → t j})
                               (inS (r (~ i)))
        side-edge : PathP B x y → I → B i1
        side-edge r i = side-square r i i1

isSetΣ : ∀{l m} {A : Set l} {B : A → Set m}
      → isSet A → ({a : A} → isSet (B a)) → isSet (Σ A B)
isSetΣ {B = B} HA HB x y p q i j = p1≡q1 i j , hcomp (λ k → λ{(i = i0) → transp (λ i → B (p1 j)) k (snd (p j))
                                                              ;(i = i1) → transp (λ i → B (q1 j)) k (snd (q j))
                                                              ;(j = i0) → transp (λ z → B (fst x)) k (snd x)
                                                              ;(j = i1) → transp (λ z → B (fst y)) k (snd y)})
                                                      (isSetPath (λ k → HB {p1≡q1 i k})
                                                                 (λ k → transp (λ z → B (p1≡q1 (i ∧ z) k)) i0 (snd (p k)))
                                                                 (λ k → transp (λ z → B (p1≡q1 (i ∨ ~ z) k)) i0 (snd (q k)))
                                                                 i j)
  where p1 = λ k → fst (p k)
        q1 = λ k → fst (q k)
        p1≡q1 : p1 ≡ q1
        p1≡q1 = HA (fst x) (fst y) p1 q1

isPropPartial : ∀ {l} {A : Set l} → isProp A →
                   (x y : A) {φ : I} (p : Partial φ (x ≡ y)) →
                   (x ≡ y) [ φ ↦ p ]
isPropPartial H x y {φ} p = inS λ i →
  hcomp (λ j → λ {(i = i0) → H x x j;
                  (i = i1) → H y y j;
                  (φ = i1) → H (H x y i) (p 1=1 i) j})
        (H x y i)
        
isSetPartial : ∀ {l} {A : Set l} → isSet A →
                 {x y : A} (p q : x ≡ y) {φ : I} (α : Partial φ (p ≡ q)) →
                 (p ≡ q) [ φ ↦ α ]
isSetPartial H = isPropPartial (H _ _)

isPropToisSet : ∀{l} {X : Set l} → isProp X → isSet X
isPropToisSet prop x y x≡y₁ x≡y₂ i j = outS (isPropPartial prop (x≡y₁ j) (x≡y₂ j) (λ{(j = i0) → refl; (j = i1) → refl})) i

transitivity-square : ∀ {l} {A : Set l} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
                        I → I → A
transitivity-square {x = x} p q i =
  hfill (λ j → λ {(i = i0) → x; (i = i1) → q j}) (inS (p i))

square-filler : ∀ {l} {A : Set l} {a b c d : A}
                  (p : a ≡ b) (q : c ≡ d) (r : a ≡ c) (s : b ≡ d) →
                  SSet l
square-filler {A = A} p q r s = (i j : I) →
  A [ (i ∨ j ∨ ~ i ∨ ~ j) ↦
      (λ {(i = i0) → p j; (i = i1) → q j;
          (j = i0) → r i; (j = i1) → s i}) ]

-- In a set, it is always possible to fill a square as above.
isSetFillSquare : ∀ {l} {A : Set l} → isSet A → {a b c d : A}
                      (p : a ≡ b) (q : c ≡ d) (r : a ≡ c) (s : b ≡ d) →
                      square-filler p q r s
isSetFillSquare {A = A} H p q r s i j =
  inS (hcomp (λ k → λ {(i = i0) → p (j ∨ ~ k);
                       (i = i1) → q j;
                       (j = i0) → transitivity-square (r ⁻¹) p (~ i) (~ k);
                       (j = i1) → H _ _ ((r ⁻¹ ∙ p) ⁻¹ ∙ q) s k i})
             (transitivity-square ((r ⁻¹ ∙ p) ⁻¹) q i j))

isPropPath : ∀{l} {B : I → Set l}
           → ({i : I} → isProp (B i))
           → (x : B i0) (y : B i1)
           → PathP B x y
isPropPath {B = B} H x y i = comp (λ k → B (i ∨ ~ k))
                                  (λ k → λ{(i = i0) → transp (λ j → B (j ∧ ~ k)) k x
                                           ;(i = i1) → y}) (H (transp B i0 x) y i)

isPropPath* : ∀{l} {B : I → I → Set l}
           → ({i j : I} → isProp (B i j))
           → (f : (i : I) → B i i0)
           → (g : (i : I) → B i i1)
           → (x : PathP (B i0) (f i0) (g i0))
           → (y : PathP (B i1) (f i1) (g i1))
           → PathP (λ i → PathP (B i) (f i) (g i)) x y
isPropPath* {B = B} H f g x y i j = hcomp
                                          (λ k → λ{(i = i0) → H (transp (λ z → B i0 (j ∧ z)) i0 (f i0)) (x j) k
                                                   ;(i = i1) → H (transp (λ z → B i1 (j ∧ z)) i0 (f i1)) (y j) k
                                                   ;(j = i0) → H (transp (λ z → B i (i0 ∧ z)) i0 (f i)) (f i) k
                                                   ;(j = i1) → H (transp (λ z → B i (i1 ∧ z)) i0 (f i)) (g i) k})
                                          (transp (λ z → B i (j ∧ z)) i0 (f i))

subst-fill : ∀{l m} {A : Set l} (P : A → Set m) {x y : A} (p : x ≡ y) (px : P x)
         → PathP (λ i → P (p i)) px (subst P p px)
subst-fill P p px i = transp (λ k → P (p (k ∧ i))) (~ i) px

abstract
  tr : ∀{l m} {A : Set l} {x y : A} (B : A → Set m)
     → x ≡ y → B x → B y
  tr B x≡y Bx = transp (λ i → B (x≡y i)) i0 Bx

  trfill : ∀{l m} {A : Set l} (P : A → Set m) {x y : A} (p : x ≡ y) (px : P x)
             → PathP (λ i → P (p i)) px (tr P p px)
  trfill P p px i = transp (λ k → P (p (k ∧ i))) (~ i) px

-- IsSet instances
record IsSet* {l} (A : Set l) : Set l where
  field
    isSet* : isSet A
open IsSet* {{...}} public

-- Heterogeneous paths
record PathH {l m} {A : Set l} (B : A → Set m) {a b : A} (x : B a) (y : B b) : Set (l ⊔ m) where
  constructor pathh
  field
    type : a ≡ b
    path : PathP (λ i → B (type i)) x y
open PathH public

infix 10 PathH
syntax PathH T x y = x ⟦ T ⟧ y

-- Heterogeneous path library
module _ {l m} {A : Set l} {B : A → Set m} where
  hrefl : {a : A} {x : B a} → x ⟦ B ⟧ x
  hrefl = pathh refl refl

  hsym : {a b : A} {x : B a} {y : B b} → x ⟦ B ⟧ y → y ⟦ B ⟧ x
  hsym p = pathh (λ i → type p (~ i)) (λ i → path p (~ i))

  private composer : {a b c : A} → a ≡ b → b ≡ c → I → I → Type m
          composer {a} a≡b b≡c i j = B (hcomp (λ k → λ{(i = i0) → a
                                                       ;(i = i1) → b≡c (j ∧ k)
                                                       ;(j = i0) → a≡b i}) (a≡b i))

  infixr 12 _●_
  _●_ : {a b c : A} {x : B a} {y : B b} {z : B c}
      → x ⟦ B ⟧ y → y ⟦ B ⟧ z → x ⟦ B ⟧ z
  type (x≡y ● y≡z) = type x≡y ∙ type y≡z
  path (x≡y ● y≡z) i = comp (composer (type x≡y) (type y≡z) i)
                            (λ k → λ{(i = i0) → path x≡y i0
                                     ;(i = i1) → path y≡z k})
                            (path x≡y i)

  hmerge : {a : A} → {x y : B a} → {{H : IsSet* A}} → x ⟦ B ⟧ y → x ≡ y
  hmerge {a} {x} {y} x≡y = subst (λ p → PathP (λ i → B (p i)) x y)
                                 (isSet* a a (type x≡y) refl)
                                 (path x≡y)

  hmerge* : {a : A} → {x y : B a} → (H : isSet A) → x ⟦ B ⟧ y → x ≡ y
  hmerge* H = hmerge {{record {isSet* = H}}}

  hcollapse : {{H : IsSet* A}} → {a b : A} {x : B a} {y : B b}
           → x ⟦ B ⟧ y → (P : a ≡ b) → PathP (λ i → B (P i)) x y
  hcollapse {a} {b} {x} {y} x≡y P = subst (λ p → PathP (λ i → B (p i)) x y)
                                          (isSet* a b (type x≡y) P)
                                          (path x≡y)

  hcollapse* : (H : isSet A) → {a b : A} {x : B a} {y : B b}
           → x ⟦ B ⟧ y → (P : a ≡ b) → PathP (λ i → B (P i)) x y
  hcollapse* H = hcollapse {{record {isSet* = H}}}

  infixl 15 ‼_
  ‼_ : {a b : A} {x : B a} {y : B b} {P : a ≡ b} → (PathP (λ i → B (P i)) x y) → x ⟦ B ⟧ y
  ‼ x≡y = pathh _ x≡y
  
  hcong : ∀ {n k} {C : Set n} {D : C → Set k}
            {f : A → C} (g : {a : A} → B a → D (f a)) {a b : A} {x : B a} {y : B b} →
        x ⟦ B ⟧ y → g x ⟦ D ⟧ g y
  hcong {f = f} g p = pathh (cong f (type p)) (dcong g (path p))

  infixr 12 _⟮_⟯_
  infixr 13 _□

  _⟮_⟯_ : {a b c : A} (x : B a) {y : B b} {z : B c} → x ⟦ B ⟧ y → y ⟦ B ⟧ z → x ⟦ B ⟧ z
  x ⟮ p ⟯ q = p ● q

  _□ : {a : A} (x : B a) → x ⟦ B ⟧ x
  x □ = hrefl

  hisSet : isSet A → ({x : A} → isSet (B x))
         → {a b : A} {x : B a} {y : B b}
         → isProp (x ⟦ B ⟧ y)
  hisSet HA HB {a} {b} {x} {y} P Q i = pathh (S i) (R i)
     where S : type P ≡ type Q
           S = HA a b (type P) (type Q)
           R : PathP (λ i → PathP (λ j → B (S i j)) x y) (path P) (path Q)
           R i j = hcomp (λ k → λ{(i = i0) → transp (λ z → B (S i0 j)) k (path P j)
                                  ;(i = i1) → transp (λ z → B (S i1 j)) k (path Q j)
                                  ;(j = i0) → transp (λ z → B a) k x
                                  ;(j = i1) → transp (λ z → B b) k y})
                         (isSetPath (λ k → HB {S i k})
                                    (λ k → transp (λ z → B (S (i ∧ z) k)) i0 (path P k))
                                    (λ k → transp (λ z → B (S (i ∨ ~ z) k)) i0 (path Q k))
                                    i j)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
-- {-# BUILTIN NATURAL ℕ #-}

zero≢suc : {n : ℕ} → zero ≡ suc n → ⊥
zero≢suc p = transport (cong (λ{zero → ⊤; (suc _) → ⊥}) p) tt

suc-elim : (n : ℕ) {m : ℕ} → n ≡ suc m → ℕ
suc-elim zero p = absurd (zero≢suc p)
suc-elim (suc x) p = x

suc-injective : {n m : ℕ} → suc n ≡ suc m → n ≡ m
suc-injective p i = suc-elim (p i) (λ k → p (i ∧ ~ k))

discreteℕ : Discrete ℕ
discreteℕ zero zero = yes refl
discreteℕ zero (suc y) = no zero≢suc
discreteℕ (suc x) zero = no (zero≢suc ∘ sym)
discreteℕ (suc x) (suc y) with discreteℕ x y
... | yes x = yes (cong suc x)
... | no x = no (λ y → x (suc-injective y))

isSetℕ : isSet ℕ
isSetℕ = discreteToisSet discreteℕ

nothing≢just : {A : Set} → {x : A} → nothing ≡ just x → ⊥
nothing≢just p = transport (cong (λ{nothing → ⊤ ; (just _) → ⊥}) p) tt

isSetMaybe : ∀{A : Set} → isSet A → isSet (Maybe A)
isSetMaybe {A = A} H nothing nothing x≡y1 x≡y2
  = x≡y1
    ≡⟨ (λ i j → nothing≡ (x≡y1 j) (λ k → x≡y1 (j ∧ k)) (~ i)) ⟩
    refl {x = nothing}
    ≡⟨ (λ i j → nothing≡ (x≡y2 j) (λ k → x≡y2 (j ∧ k)) i) ⟩
    x≡y2 ∎
  where nothing≡ : (z : Maybe A) → nothing ≡ z → nothing ≡ z
        nothing≡ nothing _ = refl
        nothing≡ (just _) p = absurd (nothing≢just p)
isSetMaybe H nothing (just x) x≡y1 x≡y2 = absurd (nothing≢just x≡y1)
isSetMaybe H (just x) nothing x≡y1 x≡y2 = absurd (nothing≢just (sym x≡y1))
isSetMaybe {A = A} H (just x) (just y) x≡y1 x≡y2 = S' ∙ (λ i j → just (H x y S T i j)) ∙ sym T'
  where just-elim : (z : Maybe A) → just x ≡ z → A
        just-elim nothing p = absurd (nothing≢just (sym p))
        just-elim (just x) p = x
        S : x ≡ y
        S k = just-elim (x≡y1 k) (λ l → x≡y1 (k ∧ l))
        T : x ≡ y
        T k = just-elim (x≡y2 k) (λ l → x≡y2 (k ∧ l))
        just-elim≡ : (z : Maybe A) → (p : just x ≡ z) → z ≡ just (just-elim z p)
        just-elim≡ nothing p = absurd (nothing≢just (sym p))
        just-elim≡ (just x) p = refl
        S' : x≡y1 ≡ cong just S
        S' l k = just-elim≡ (x≡y1 k) (λ l → x≡y1 (k ∧ l)) l
        T' : x≡y2 ≡ cong just T
        T' l k = just-elim≡ (x≡y2 k) (λ l → x≡y2 (k ∧ l)) l        

discreteBool : Discrete Bool
discreteBool false false = yes refl
discreteBool false true = no λ p → true≢false (sym p)
discreteBool true false = no true≢false
discreteBool true true = yes refl

isSetBool : isSet Bool
isSetBool = discreteToisSet discreteBool
