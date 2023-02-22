{-# OPTIONS --cubical --allow-unsolved-metas #-}
module EvaluatorSC where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Agda.Primitive
open import Library
open import Syntax
open import Lemmas
open import Weakening
open import Values
open import NormalForm
open import EvalSpec
open import Stability
open import TypeEval

private variable n : ℕ

-- This is here because TypeEval can handle without weakening
[○]TyP : {S : TySk} {n : ℕ} {X Y Z : Con} {A : TyP S n Z} {s : Wk Y Z} {a : Wk X Y}
       → A [ ⌜ s ○ a ⌝Wk ]TyP ≡ (A [ ⌜ s ⌝Wk ]TyP) [ ⌜ a ⌝Wk ]TyP
[○]TyP {S} {n} {X} {Y} {Z} {A} {s} {a}
       = A [ ⌜ s ○ a ⌝Wk ]TyP
         ≡⟨ cong (A [_]TyP) ⌜○⌝ ⟩
         (A [ ⌜ s ⌝Wk ∘t ⌜ a ⌝Wk ]TyP)
         ≡⟨ [∘]TyP ⟩
         A [ ⌜ s ⌝Wk ]TyP [ ⌜ a ⌝Wk ]TyP ∎

scvP : {S : TySk} {n : ℕ} {X : Con} → {A : TyP S n X} → Val n X ⌜ A ⌝TyP → Set
scvP {U} {X = X} {A = U n} v = Σ[ w ∈ Nf _ X (U n) ] quot v w
scvP {El} {X = X} {A = El u} v = Σ[ w ∈ Nf _ X (El u) ] quot v w
scvP {Pi S T} {X = X} {A = Pi A B} f = {Y : Con} (a : Wk Y X) (v : Val _ Y (⌜ A [ ⌜ a ⌝Wk ]TyP ⌝TyP)) → scvP v
                            → Σ[ C ∈ TyP T _ Y ] Σ[ w ∈ Val _ Y ⌜ C ⌝TyP ]
                              (apply (subst (Val _ Y) Pi[] (f [ a ]Val)) (subst (Val _ _) ⌜[]TyP⌝ v) w × scvP w)

scv : {X : Con} {A : Ty n X} → Val n X A → Set
scv {A = A} v = scvP (subst (Val _ _) tyev v)

sce : {X Y : Con} → Env X Y → Set
sce {Y = ∅} _ = ⊤
sce {Y = Y , A} (env (p , x)) = sce p × scv x

_[_]scvP : {S : TySk} {n : ℕ} {X Y : Con} {A : TyP S n X} {v : Val n X ⌜ A ⌝TyP}
        → scvP v → (s : Wk Y X) → scvP (subst (Val n Y) (sym ⌜[]TyP⌝) (v [ s ]Val))
_[_]scvP {U} {A = U n} {v} (w , qw) s = subst (Nf (suc n) _) U[] (w [ s ]Nf)
                                 , transport (λ i → quot (subst-filler (Val _ _) U[] (v [ s ]Val) i)
                                                          (subst-filler (Nf _ _) U[] (w [ s ]Nf) i))
                                             (qw [ s ]quot)
_[_]scvP {El} {A = El u} {v} (w , qw) s = subst (Nf _ _) El[] (w [ s ]Nf)
                                   , transport (λ i → quot (subst-filler (Val _ _) El[] (v [ s ]Val) i)
                                                            (subst-filler (Nf _ _) El[] (w [ s ]Nf) i))
                                               (qw [ s ]quot)
_[_]scvP {Pi S T} {n} {X} {Z} {A = Pi A B} {v} sc s {Y} a w scw = (fst SC , fst (snd SC) , AP' , SCP)
   where SC = sc (s ○ a) (subst (λ i → Val _ _ ⌜ i ⌝TyP) (sym [○]TyP) w)
                         ((transport (λ i → scvP (subst-filler (λ i → Val _ _ ⌜ i ⌝TyP) (sym [○]TyP) w i)) scw))
         X1 = (⌜ A ⌝TyP [ ⌜ s ○ a ⌝Wk ]T)
         X2 = (⌜ A [ ⌜ s ⌝Wk ]TyP ⌝TyP [ ⌜ a ⌝Wk ]T)
         X1≡X2 : X1 ⟦ Ty _ ⟧ X2
         X1≡X2 = X1
                 ⟮ ‼ cong (⌜ A ⌝TyP [_]T) ⌜○⌝ ⟯
                 ⌜ A ⌝TyP [ ⌜ s ⌝Wk ∘t ⌜ a ⌝Wk ]T
                 ⟮ ‼ [∘]T ⟯
                 (⌜ A ⌝TyP [ ⌜ s ⌝Wk ]T) [ ⌜ a ⌝Wk ]T
                 ⟮ ‼ cong (_[ ⌜ a ⌝Wk ]T) (sym ⌜[]TyP⌝) ⟯
                 X2 □
         Y1 = (⌜ B ⌝TyP [ (⌜ s ○ a ⌝Wk ↑ ⌜ A ⌝TyP) ]T)
         Y2 = (⌜ (subst (λ i → TyP T n (Z , i)) (sym ⌜[]TyP⌝) (B [ ⌜ s ⌝Wk ↑ ⌜ A ⌝TyP ]TyP)) ⌝TyP [ (⌜ a ⌝Wk ↑ ⌜ (A [ ⌜ s ⌝Wk ]TyP) ⌝TyP) ]T)
         Y1≡Y2 : Y1 ⟦ Ty _ ⟧ Y2
         Y1≡Y2 = Y1
                 ⟮ ‼ dcong (λ i → ⌜ B ⌝TyP [ i ↑ ⌜ A ⌝TyP ]T) ⌜○⌝ ⟯
                 (⌜ B ⌝TyP [ (⌜ s ⌝Wk ∘t ⌜ a ⌝Wk) ↑ ⌜ A ⌝TyP ]T)
                 ⟮ hcong (⌜ B ⌝TyP [_]T) (hsym ↑∘↑) ⟯
                 (⌜ B ⌝TyP [ (⌜ s ⌝Wk ↑ ⌜ A ⌝TyP) ∘t (⌜ a ⌝Wk ↑ (⌜ A ⌝TyP [ ⌜ s ⌝Wk ]T)) ]T)
                 ⟮ ‼ [∘]T ⟯
                 ((⌜ B ⌝TyP [ ⌜ s ⌝Wk ↑ ⌜ A ⌝TyP ]T) [ ⌜ a ⌝Wk ↑ (⌜ A ⌝TyP [ ⌜ s ⌝Wk ]T) ]T)
                 ⟮ ‼ dcong (_[ ⌜ a ⌝Wk ↑ (⌜ A ⌝TyP [ ⌜ s ⌝Wk ]T) ]T) (sym ⌜[]TyP⌝) ⟯
                 (⌜ B [ ⌜ s ⌝Wk ↑ ⌜ A ⌝TyP ]TyP ⌝TyP [ ⌜ a ⌝Wk ↑ (⌜ A ⌝TyP [ ⌜ s ⌝Wk ]T) ]T)
                 ⟮ ‼ dcong (λ {k} i → ⌜ i ⌝TyP [ (⌜ a ⌝Wk ↑ sym (⌜[]TyP⌝ {A = A}) k) ]T) (subst-filler (λ i → TyP T n (Z , i)) (sym ⌜[]TyP⌝) (B [ ⌜ s ⌝Wk ↑ ⌜ A ⌝TyP ]TyP))  ⟯
                 Y2 □
         A1 = (subst (Val n Y) Pi[] (v [ s ○ a ]Val))
         A2 = (subst (Val _ _) Pi[] (subst (Val _ _) (sym ⌜[]TyP⌝) (v [ s ]Val) [ a ]Val))
         A1≡A2 : A1 ⟦ Val _ _ ⟧ A2
         A1≡A2 = A1
                 ⟮ ‼ sym (subst-filler (Val _ _) Pi[] (v [ s ○ a ]Val)) ⟯
                 v [ s ○ a ]Val
                 ⟮ ‼ [○]Val {v = v} ⟯
                 subst (Val n Y) ○-lemma ((v [ s ]Val) [ a ]Val)
                 ⟮ ‼ sym (subst-fill (Val _ _) ○-lemma ((v [ s ]Val) [ a ]Val)) ⟯
                 v [ s ]Val [ a ]Val
                 ⟮ ‼ dcong (_[ a ]Val) (subst-filler (Val _ _) (sym ⌜[]TyP⌝) (v [ s ]Val)) ⟯
                 subst (Val _ _) (sym ⌜[]TyP⌝) (v [ s ]Val) [ a ]Val
                 ⟮ ‼ subst-filler (Val _ _) Pi[] (subst (Val _ _) (sym ⌜[]TyP⌝) (v [ s ]Val) [ a ]Val) ⟯
                 A2 □
         B1 = (subst (Val _ _) ⌜[]TyP⌝ (subst (λ i → Val _ _ ⌜ i ⌝TyP) (sym [○]TyP) w))
         B2 = (subst (Val _ _) ⌜[]TyP⌝ w)
         B1≡B2 : B1 ⟦ Val _ _ ⟧ B2
         B1≡B2 = B1
                 ⟮ ‼ sym (subst-filler (Val _ _) ⌜[]TyP⌝ (subst (λ i → Val _ _ ⌜ i ⌝TyP) (sym [○]TyP) w)) ⟯
                 (subst (λ i → Val _ _ ⌜ i ⌝TyP) (sym [○]TyP) w)
                 ⟮ ‼ sym (subst-filler (λ i → Val _ _ ⌜ i ⌝TyP) (sym [○]TyP) w) ⟯
                 w
                 ⟮ ‼ subst-filler (Val _ _) ⌜[]TyP⌝ w ⟯
                 B2 □
         AP : apply A1 B1 (fst (snd SC))
         AP = fst (snd (snd SC))
         AP' : apply A2 B2 (fst (snd SC))
         AP' = transport (λ i → apply (hcollapse A1≡A2 (dcong₂ (λ x y → term.Pi x y) (hmerge X1≡X2) (hcollapse Y1≡Y2 (cong (Y Con.,_) (hmerge X1≡X2)))) i)
                                       (hcollapse B1≡B2 (hmerge X1≡X2) i)
                                       (fst (snd SC))) AP
         SCP : scvP (fst (snd SC))
         SCP = snd (snd (snd SC))

_[_]scv : {n : ℕ} {X Y : Con} {A : Ty n X} {v : Val n X A}
        → scv v → (s : Wk Y X) → scv (v [ s ]Val)
_[_]scv {n} {X} {Y} {A} {v} sv s
  = transport (λ i → scvP (hcollapse P (dcong ⌜_⌝TyP (hcollapse ⌜[]ev⌝ (type ⌜[]ev⌝))) i)) (sv [ s ]scvP)
  where P : subst (Val _ _) (sym ⌜[]TyP⌝) (subst (Val _ _) tyev v [ s ]Val) ⟦ Val _ _ ⟧ subst (Val _ _) tyev (v [ s ]Val)
        P = subst (Val _ _) (sym ⌜[]TyP⌝) (subst (Val _ _) tyev v [ s ]Val)
            ⟮ ‼ sym (subst-filler (Val _ _) (sym ⌜[]TyP⌝) (subst (Val _ _) tyev v [ s ]Val)) ⟯
            subst (Val _ _) tyev v [ s ]Val
            ⟮ ‼ dcong (_[ s ]Val) (sym (subst-filler (Val _ _) tyev v)) ⟯
            v [ s ]Val
            ⟮ ‼ subst-filler (Val _ _) tyev (v [ s ]Val) ⟯
            subst (Val n Y) tyev (v [ s ]Val) □

_[_]sce : {X Y Z : Con} → {p : Env Y Z} → sce p → (s : Wk X Y) → sce (p [ s ]Env)
_[_]sce {Z = ∅} sc s = tt
_[_]sce {Z = Z , A} {env (p , x)} (sp , sx) s = sp [ s ]sce
                                              , transport (λ i → scv (trfill (Val _ _) (sym [[]Env]) (x [ s ]Val) i)) (_[_]scv {v = x} sx s)


isPropScv : {S : TySk} {n : ℕ} {X : Con} {A : TyP S n X} {v : Val n X ⌜ A ⌝TyP} → isProp (scvP v)
isPropScv {.U} {.(suc n)} {X} {U n} {v} (w , qw) (w' , qw') i = quot-sound qw qw' i , isPropPath {B = λ i → quot v (quot-sound qw qw' i)} isPropQuot qw qw' i
isPropScv {.El} {n} {X} {El x} {v} (w , qw) (w' , qw') i = quot-sound qw qw' i , isPropPath {B = λ i → quot v (quot-sound qw qw' i)} isPropQuot qw qw' i
isPropScv {.(Pi _ _)} {n} {X} {Pi A B} {f} scf scf' i a v sv = let
    (B , b , ab , sb) = scf a v sv
    (B' , b' , ab' , sb') = scf' a v sv
    ap = applySound ab ab'
    P = evty {A = B} ● (‼ cong ev (type ap)) ● hsym (evty {A = B'})
    X = hmerge P
    Y = hcollapse ap (cong ⌜_⌝TyP X)
    Z = (subst (Val _ _) Pi[] (f [ a ]Val))
    v' = subst (Val _ _) ⌜[]TyP⌝ v
    in X i
     , Y i
     , isPropPath {B = λ i → apply Z v' (Y i)} isPropApply ab ab' i
     , isPropPath {B = λ i → scvP (Y i)} isPropScv sb sb' i

isPropSce : {X Y : Con} {p : Env X Y} → isProp (sce p)
isPropSce {X} {∅} {p} tt tt = refl
isPropSce {X} {Y , A} {env (p , x)} (scp , scx) (scp' , scx') = cong₂ {C = λ _ _ → sce p × scvP (subst (Val _ _) tyev x)} (_,_) (isPropSce scp scp') (isPropScv scx scx')

scvP-quot : {S : TySk} {n : ℕ} {X : Con} {A : TyP S n X}
        → {v : Val n X ⌜ A ⌝TyP} → scvP v
        → Σ[ n ∈ Nf n X ⌜ A ⌝TyP ] quot v n

scvP-unquot : {S : TySk} {n : ℕ} {X : Con} {A : TyP S n X}
          → {v : Sus n X ⌜ A ⌝TyP} → (w : Nu n X ⌜ A ⌝TyP) → quots v w
          → scvP (neu v)

scvP-var : {S : TySk} {n : ℕ} {X : Con} {A : TyP S n X} {x : In n X ⌜ A ⌝TyP} → scvP {A = A} (neu (var x))
scvP-var {A = A} {x} = scvP-unquot (var x) quotsvar

abstract
  TyP[wk] : {S : TySk} {n : ℕ} {X : Con} {A : TyP S n X}
          → ⌜ A ⌝TyP [ wk {A = ⌜ A ⌝TyP} ]T ≡ ⌜ A [ ⌜ weakener ⌜ A ⌝TyP idwk ⌝Wk ]TyP ⌝TyP
  TyP[wk] {A = A} = ⌜ A ⌝TyP [ wk ]T
                    ≡⟨ idwk-lemma ⟩
                    ⌜ A ⌝TyP [ ⌜ weakener ⌜ A ⌝TyP idwk ⌝Wk ]T
                    ≡⟨ sym ⌜[]TyP⌝ ⟩
                    ⌜ A [ ⌜ weakener ⌜ A ⌝TyP idwk ⌝Wk ]TyP ⌝TyP ∎

  ⌜weakener-idwk⌝ : {X : Con} {A : Ty n X}
                 → ⌜ weakener A idwk ⌝Wk ≡ wk {A = A}
  ⌜weakener-idwk⌝ {A = A} = ⌜ weakener A idwk ⌝Wk
                           ≡⟨ ⌜weakener⌝ ⟩
                           ⌜ idwk ⌝Wk ∘t wk
                           ≡⟨ cong (_∘t wk) ⌜idwk⌝ ⟩
                           idt ∘t wk
                           ≡⟨ id∘ ⟩
                           wk ∎   

scvP-quot {.U} {.(suc n)} {X} {U n} {v} sv = sv
scvP-quot {.El} {n} {X} {El x} {v} sv = sv
scvP-quot {.(Pi _ _)} {n} {X} {Pi A B} {f} sf = let
          varz : In n (X , ⌜ A ⌝TyP) (⌜ A [ ⌜ weakener _ idwk ⌝Wk ]TyP ⌝TyP)
          varz = subst (In _ _) TyP[wk] (Zero)
          (C , fz , afz , scfz) = sf (weakener _ idwk) (neu (var varz)) (scvP-var {x = varz})
          (nfz , qfz) = scvP-quot scfz
          p : ⌜ subst (Val _ _) (⌜[]TyP⌝) (neu (var varz)) ⌝Val ⟦ Tm _ _ ⟧ vz
          p = ⌜ subst (Val _ _) (⌜[]TyP⌝) (neu (var varz)) ⌝Val
              ⟮ ‼ dcong (⌜_⌝Val) (sym (subst-filler (Val _ _) (⌜[]TyP⌝) (neu (var varz)))) ⟯
              ⌜ subst (In _ _) TyP[wk] Zero ⌝In
              ⟮ ‼ dcong (⌜_⌝In) (sym (subst-filler (In _ _) TyP[wk] Zero)) ⟯
              vz □
          C≡B : C ≡ B
          C≡B = TyP-injective (⌜ C ⌝TyP
                              ≡⟨ sym (type (apply≡ afz)) ⟩
                              ⌜ B ⌝TyP [ ⌜ weakener ⌜ A ⌝TyP idwk ⌝Wk ↑ ⌜ A ⌝TyP ]T [ < ⌜ subst (Val _ _) ⌜[]TyP⌝ (neu (var varz)) ⌝Val > ]T
                              ≡⟨ sym [∘]T ⟩
                              ⌜ B ⌝TyP [ (⌜ weakener ⌜ A ⌝TyP idwk ⌝Wk ↑ ⌜ A ⌝TyP) ∘t < ⌜ subst (Val _ _) ⌜[]TyP⌝ (neu (var varz)) ⌝Val > ]T
                              ≡⟨ cong (⌜ B ⌝TyP [_]T) ↑∘<> ⟩
                              ⌜ B ⌝TyP [ (⌜ weakener ⌜ A ⌝TyP idwk ⌝Wk , ⌜ subst (Val _ _) ⌜[]TyP⌝ (neu (var varz)) ⌝Val) ]T
                              ≡⟨ (λ i → ⌜ B ⌝TyP [ ⌜weakener-idwk⌝ i , hcollapse p (cong (⌜ A ⌝TyP [_]T) ⌜weakener-idwk⌝) i ]T) ⟩
                              ⌜ B ⌝TyP [ wk , vz ]T
                              ≡⟨ cong (⌜ B ⌝TyP [_]T) πη ⟩
                              ⌜ B ⌝TyP [ idt ]T
                              ≡⟨ [id]T ⟩
                              ⌜ B ⌝TyP ∎)
          fz' : Val n (X , ⌜ A ⌝TyP) ⌜ B ⌝TyP
          fz' = subst (λ i → Val _ _ ⌜ i ⌝TyP) C≡B fz
          nfz' : Nf n (X , ⌜ A ⌝TyP) ⌜ B ⌝TyP
          nfz' = subst (λ i → Nf _ _ ⌜ i ⌝TyP) C≡B nfz
          r : subst (Val _ _) ⌜[]TyP⌝ (neu (var varz)) ⟦ Val _ _ ⟧ tr (Val _ _) idwk-lemma (neu (var Zero))
          r = subst (Val _ _) ⌜[]TyP⌝ (neu (var varz))
              ⟮ ‼ sym (subst-filler (Val _ _) ⌜[]TyP⌝ (neu (var varz))) ⟯
              neu (var varz)
              ⟮ ‼ dcong (λ i → Val.neu (var i)) (sym (subst-filler (In _ _) TyP[wk] Zero))  ⟯
              neu (var Zero)
              ⟮ ‼ trfill (Val _ _) idwk-lemma (neu (var Zero)) ⟯
              tr (Val _ _) idwk-lemma (neu (var Zero)) □
          afz' : apply (subst (Val _ _) Pi[] (f [ weakener _ idwk ]Val))
                       (tr (Val _ _) idwk-lemma (neu (var Zero)))
                       fz'
          afz' = transport (λ i → apply (subst (Val _ _) Pi[] (f [ weakener _ idwk ]Val))
                                         (hmerge r i)
                                         (subst-filler (λ i → Val _ _ ⌜ i ⌝TyP) C≡B fz i)) afz
          qfz' : quot fz' nfz'
          qfz' = transport (λ i → quot (subst-filler (λ i → Val _ _ ⌜ i ⌝TyP) C≡B fz i)
                                        (subst-filler (λ i → Nf _ _ ⌜ i ⌝TyP) C≡B nfz i)) qfz 
          in lam nfz' , quotPi afz' qfz'

scvP-unquot {.U} {.(suc n)} {X} {U n} {v} w qv = neuU w , quotU qv
scvP-unquot {.El} {n} {X} {El x} {v} w qv = neuEl w , quotEl qv
scvP-unquot {.(Pi _ _)} {n} {X} {Pi A B} {f} fn qf {Y} a v sv = let
            (m , qm) = scvP-quot sv
            f+ : Sus n Y (Pi ⌜ A ⌝TyP ⌜ B ⌝TyP [ ⌜ a ⌝Wk ]T)
            f+ = f [ a ]Sus
            f+' : Sus n Y (Pi (⌜ A ⌝TyP [ ⌜ a ⌝Wk ]T) (⌜ B ⌝TyP [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyP ]T))
            f+' = subst (Sus _ _) Pi[] f+
            neuf+' : Val n Y (Pi (⌜ A ⌝TyP [ ⌜ a ⌝Wk ]T) (⌜ B ⌝TyP [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyP ]T))
            neuf+' = subst (Val _ _) Pi[] (neu f+)
            p : neu f+' ⟦ Val _ _ ⟧ neuf+'
            p = neu f+'
                ⟮ ‼ dcong Val.neu (sym (subst-filler (Sus _ _) Pi[] f+)) ⟯
                neu f+
                ⟮ ‼ subst-filler (Val _ _) Pi[] (neu f+) ⟯
                neuf+' □
            v' : Val n Y (⌜ A ⌝TyP [ ⌜ a ⌝Wk ]T)
            v' = subst (Val _ _) (⌜[]TyP⌝) v
            C : Ty n Y
            C = ⌜ B ⌝TyP [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyP ]T [ < ⌜ v' ⌝Val > ]T
            C' : Ty n Y
            C' = ⌜ B [ ⌜ a ⌝Wk , ⌜ v' ⌝Val ]TyP ⌝TyP
            C≡C' : C ≡ C'
            C≡C' = ⌜ B ⌝TyP [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyP ]T [ < ⌜ v' ⌝Val > ]T
                   ≡⟨ sym [∘]T ⟩
                   ⌜ B ⌝TyP [ (⌜ a ⌝Wk ↑ ⌜ A ⌝TyP) ∘t < ⌜ v' ⌝Val > ]T
                   ≡⟨ cong (⌜ B ⌝TyP [_]T) ↑∘<> ⟩
                   ⌜ B ⌝TyP [ (⌜ a ⌝Wk , ⌜ v' ⌝Val) ]T
                   ≡⟨ sym ⌜[]TyP⌝ ⟩
                   ⌜ B [ ⌜ a ⌝Wk , ⌜ v' ⌝Val ]TyP ⌝TyP ∎
            fv = Sus.app f+' v'
            afv = apply.neu {sv = f+'} {v = v'}
            fv' = subst (Sus n Y) C≡C' fv
            afv' : apply neuf+' v' (neu fv')
            afv' = transport (λ i → apply (hmerge p i) v' (neu (subst-fill (Sus n Y) C≡C' fv i))) afv
            fn+ = fn [ a ]Nu
            fn+' = subst (Nu n Y) Pi[] fn+
            m' = subst (Nf n Y) ⌜[]TyP⌝ m
            qf' : quots f+' fn+'
            qf' = transport (λ i → quots (subst-filler (Sus n Y) Pi[] f+ i)
                                          (subst-filler (Nu n Y) Pi[] fn+ i)) (qf [ a ]quots)
            qm' : quot v' m'
            qm' = transport (λ i → quot (subst-filler (Val n Y) ⌜[]TyP⌝ v i)
                                         (subst-filler (Nf n Y) ⌜[]TyP⌝ m i)) qm
            fm = Nu.app fn+' m'
            fm' = tr (λ i → Nu n Y (⌜ B ⌝TyP [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyP ]T [ < i > ]T)) (sym (quot≡ qm')) fm
            qfv : quots fv fm'
            qfv = quotsapp qf' qm'
            fm'' = subst (Nu n Y) C≡C' fm'
            qfv' : quots fv' fm''
            qfv' = transport (λ i → quots (subst-filler (Sus n Y) C≡C' fv i)
                                           (subst-filler (Nu n Y) C≡C' fm' i)) qfv
            in B [ ⌜ a ⌝Wk , ⌜ v' ⌝Val ]TyP , neu fv' , afv' , scvP-unquot fm'' qfv'

scv-quot : {X : Con} {A : Ty n X} {v : Val n X A} → scv v → Σ[ w ∈ Nf n X A ] quot v w
scv-quot {A = A} {v} sv = let
  w , qv = scvP-quot sv
  p = subst-filler (Val _ _) tyev v
  q = subst-filler (Nf _ _) (sym tyev) w
  in subst (Nf _ _) (sym tyev) w , transport (λ i → quot (p (~ i)) (q i)) qv

scv-unquot : {X : Con} {A : Ty n X} {v : Sus n X A} (w : Nu n X A) → quots v w → scv (neu v)
scv-unquot {A = A} {v} w qv = let
  p = subst-filler (Sus _ _) tyev v
  q = subst-filler (Nu _ _) tyev w
  sv : scvP (neu (subst (Sus _ _) tyev v))
  sv = scvP-unquot (subst (Nu _ _) tyev w) (transport (λ i → quots (p i) (q i)) qv)
  r : neu (subst (Sus _ _) tyev v) ⟦ Val _ _ ⟧ subst (Val _ _) tyev (neu v)
  r = neu (subst (Sus _ _) tyev v)
      ⟮ ‼ dcong Val.neu (sym (subst-fill (Sus _ _) tyev v)) ⟯
      neu v
      ⟮ ‼ subst-filler (Val _ _) tyev (neu v) ⟯
      subst (Val _ _) tyev (neu v) □
  in tr scvP (hmerge r) sv

scv-id : {X : Con} {A : Ty n X} {x : In n X A} → scv (neu (var x))
scv-id {x = x} = scv-unquot (var x) quotsvar

sce-idenv : (X : Con) → sce (idenv {X})
sce-idenv ∅ = tt
sce-idenv (X , A) = sce-idenv X [ weakener _ idwk ]sce , transport (λ i → scv (trfill (Val _ _) ([⌜id[E]⌝] {A = A}) (neu (var Zero)) i)) scv-id

isPropEvalScv : {X Y : Con} {A : Ty n Y} {u : Tm n Y A} {p : Env X Y}
             → isProp (Σ[ B ∈ Ty n X ] Σ[ v ∈ Val n X B ] eval u p v × scv v)

isPropEvalsSce : {X Y Z : Con} {s : Tms Y Z} {p : Env X Y}
             → isProp (Σ[ v ∈ Env X Z ] evals s p v × sce v)

isPropEvalScv {n} {X} {Y} {A} {u} {p} (B , x , ex , sx) (B' , x' , ex' , sx') i
  = type (evalSound ex ex') i
  , path (evalSound ex ex') i
  , isPropPath {B = λ i → eval u p (path (evalSound ex ex') i)} isPropEval ex ex' i
  , isPropPath {B = λ i → scv (path (evalSound ex ex') i)} isPropScv sx sx' i

isPropEvalsSce {X} {Y} {Z} {s} {p} (v , es , sv) (v' , es' , sv') i
  = evalsSound es es' i
  , isPropPath {B = λ i → evals s p (evalsSound es es' i)} isPropEvals es es' i
  , isPropPath {B = λ i → sce (evalsSound es es' i)} isPropSce sv sv' i
