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
open import SCVA

private variable n : ℕ

_[_]scv* : {n : ℕ} {X Y : Con} {A : TyS n X} {v : Val n X ⌜ A ⌝TyS}
        → scv _ v → (s : Wk Y X) → scv _ (v [ s ]Val)
_[_]scv* {A = U n} {v} sv s = let
     (w , qv) = scv-access-U v sv
     nsv : scv (U n) (subst (Val _ _) U[] (v [ s ]Val))
     nsv = scv-mk-U (subst (Val _ _) U[] (v [ s ]Val)) (subst (Nf _ _) U[] (w [ s ]Nf) , transport (λ i → quot (subst-filler (Val _ _) U[] (v [ s ]Val) i)
                                                                                                                (subst-filler (Nf _ _) U[] (w [ s ]Nf) i))
                                                                                                   (qv [ s ]quot))
     in transport (λ i → scv (U[] (~ i)) (subst-filler (Val _ _) U[] (v [ s ]Val) (~ i))) nsv
_[_]scv* {A = El u} {v} sv s = let
     (w , qv) = scv-access-El v sv
     nsv = scv-mk-El (subst (Val _ _) El[] (v [ s ]Val)) (subst (Nf _ _) El[] (w [ s ]Nf) , transport (λ i → quot (subst-filler (Val _ _) El[] (v [ s ]Val) i)
                                                                                                                (subst-filler (Nf _ _) El[] (w [ s ]Nf) i))
                                                                                                   (qv [ s ]quot))
     in transport (λ i → scv (El[] (~ i)) (subst-filler (Val _ _) El[] (v [ s ]Val) (~ i))) nsv
_[_]scv* {A = Pi A B} {f} sf s = let
     sf' = scv-mk-Pi (subst (Val _ _) Pi[] (f [ s ]Val)) (λ {Y} a v sv → let
                     sv' = transport (λ i → scv (○-lemma i) (subst-filler (Val _ _) ○-lemma v i)) sv
                     (w , afw , sw) = scv-access-Pi f sf (s ○ a) (subst (Val _ _) ○-lemma v) sv'
                     A0 = ⌜ subst (Val _ _) ○-lemma v ⌝Val
                     A1 = subst (Tm _ _) (sym [∘]T) ⌜ v ⌝Val
                     A0≡A1 : A0 ⟦ Tm _ _ ⟧ A1
                     A0≡A1 = A0
                             ⟮ ‼ dcong ⌜_⌝Val (sym (subst-filler (Val _ _) ○-lemma v)) ⟯
                             ⌜ v ⌝Val
                             ⟮ ‼ subst-filler (Tm _ _) (sym [∘]T) ⌜ v ⌝Val ⟯
                             A1 □
                     B0 = ⌜ B ⌝TyS [ ⌜ s ○ a ⌝Wk , ⌜ subst (Val _ _) ○-lemma v ⌝Val ]T
                     B1 = ⌜ B ⌝TyS [ (⌜ s ⌝Wk ↑ ⌜ A ⌝TyS) ]T [ ⌜ a ⌝Wk , ⌜ v ⌝Val ]T
                     B0≡B1 : B0 ⟦ Ty _ ⟧ B1
                     B0≡B1 = B0
                             ⟮ ‼ dcong₂ (λ i j → ⌜ B ⌝TyS [ i , j ]T) ⌜○⌝ (hcollapse A0≡A1 (cong (⌜ A ⌝TyS [_]T) ⌜○⌝)) ⟯
                             ((⌜ B ⌝TyS [ (⌜ s ⌝Wk ∘t ⌜ a ⌝Wk) , subst (Tm _ _) (sym [∘]T) ⌜ v ⌝Val ]T))
                             ⟮ ‼ cong (⌜ B ⌝TyS [_]T) (sym ↑∘,) ⟯
                             ⌜ B ⌝TyS [ (⌜ s ⌝Wk ↑ ⌜ A ⌝TyS) ∘t (⌜ a ⌝Wk , ⌜ v ⌝Val) ]T
                             ⟮ ‼ [∘]T ⟯
                             B1 □
                     FS0 = subst (Val _ _) Pi[] (f [ s ○ a ]Val)
                     FS1 = subst (Val _ _) Pi[] (subst (Val _ _) Pi[] (f [ s ]Val) [ a ]Val)
                     FS0≡FS1 : FS0 ⟦ Val _ _ ⟧ FS1
                     FS0≡FS1 = FS0
                               ⟮ ‼ sym (subst-filler (Val _ _) Pi[] (f [ s ○ a ]Val)) ⟯
                               f [ s ○ a ]Val
                               ⟮ ‼ [○]Val {v = f} ⟯
                               subst (Val _ _) ○-lemma (f [ s ]Val [ a ]Val)
                               ⟮ ‼ sym (subst-filler (Val _ _) ○-lemma (f [ s ]Val [ a ]Val)) ⟯
                               f [ s ]Val [ a ]Val
                               ⟮ ‼ dcong (_[ a ]Val) (subst-filler (Val _ _) Pi[] (f [ s ]Val)) ⟯
                               subst (Val _ _) Pi[] (f [ s ]Val) [ a ]Val
                               ⟮ ‼ subst-filler (Val _ _) Pi[] (subst (Val _ _) Pi[] (f [ s ]Val) [ a ]Val) ⟯
                               FS1 □
                     C0 = ⌜ B ⌝TyS [ ⌜ s ○ a ⌝Wk ↑ ⌜ A ⌝TyS ]T
                     C1 = ⌜ B ⌝TyS [ ⌜ s ⌝Wk ↑ ⌜ A ⌝TyS ]T [ ⌜ a ⌝Wk ↑ (⌜ A ⌝TyS [ ⌜ s ⌝Wk ]T) ]T
                     C0≡C1 : C0 ⟦ Ty _ ⟧ C1
                     C0≡C1 = C0
                             ⟮ ‼ cong (λ i → ⌜ B ⌝TyS [ i ↑ ⌜ A ⌝TyS ]T) ⌜○⌝ ⟯
                             ⌜ B ⌝TyS [ (⌜ s ⌝Wk ∘t ⌜ a ⌝Wk) ↑ ⌜ A ⌝TyS ]T
                             ⟮ hcong (⌜ B ⌝TyS [_]T) (hsym ↑∘↑) ⟯
                             ⌜ B ⌝TyS [ (⌜ s ⌝Wk ↑ ⌜ A ⌝TyS) ∘t (⌜ a ⌝Wk ↑ (⌜ A ⌝TyS [ ⌜ s ⌝Wk ]T)) ]T
                             ⟮ ‼ [∘]T ⟯
                             (⌜ B ⌝TyS [ ⌜ s ⌝Wk ↑ ⌜ A ⌝TyS ]T) [ ⌜ a ⌝Wk ↑ (⌜ A ⌝TyS [ ⌜ s ⌝Wk ]T) ]T □
                     -- apply FS0 (subst (Val n Y) ○-lemma v) w
                     afw' : apply FS1 v (subst (Val _ _) (hmerge B0≡B1) w)
                     afw' = transport (λ i → apply {--{B = hcollapse C0≡C1 (cong (_ ,_) (sym ○-lemma)) i}--} (hcollapse FS0≡FS1 (cong₂ term.Pi (sym ○-lemma) (hcollapse C0≡C1 ((cong (_ ,_) (sym ○-lemma))))) i) (subst-filler (Val _ _) ○-lemma v (~ i)) (subst-filler (Val _ _) (hmerge B0≡B1) w i)) afw
                     sw' : scv B1 (subst (Val _ _) (hmerge B0≡B1) w)
                     sw' = transport (λ i → scv (hmerge B0≡B1 i) (subst-filler (Val _ _) (hmerge B0≡B1) w i)) sw
                     in subst (Val _ _) (hmerge B0≡B1) w , afw' , sw')
     in transport (λ i → scv (Pi[] (~ i)) (subst-filler (Val _ _) Pi[] (f [ s ]Val) (~ i))) sf'

abstract
  _[_]scv : {n : ℕ} {X Y : Con} {A : Ty n X} {v : Val n X A}
          → scv _ v → (s : Wk Y X) → scv _ (v [ s ]Val)
  _[_]scv {n} {X} {Y} {A} {v} = transport (λ i → {A : TyS≡Ty {n} {X} i}
                                          → {v : Val n X (⌜ i ∶ A ⌝TyS≡Ty)}
                                          → scv _ v → (s : Wk Y X) → scv _ (v [ s ]Val))
                                          (λ {A} {v} → _[_]scv* {n} {X} {Y} {A} {v}) {A} {v}

abstract
  _[_]sce : {X Y Z : Con} → {p : Env Y Z} → sce p → (s : Wk X Y) → sce (p [ s ]Env)
  _[_]sce {Z = ∅} sc s = tt
  _[_]sce {Z = Z , A} {env (p , x)} (sp , sx) s = sp [ s ]sce
                                                , transport (λ i → scv _ (trfill (Val _ _) (sym [[]Env]) (x [ s ]Val) i)) (_[_]scv {v = x} sx s)

isPropScvB : {X : Con} {A : TyS n X} {acc : TmsAcc A} {v : Val n X ⌜ A ⌝TyS} → isProp (scvB A acc v)
isPropScvB {.(suc n)} {X} {U n} {acc} {v} (w , qv) (w' , qv') i
  = quot-sound qv qv' i
  , isPropPath (λ {i} → isPropQuot {w = quot-sound qv qv' i}) qv qv' i 
isPropScvB {n} {X} {El u} {acc} {v} (w , qv) (w' , qv') i
  = quot-sound qv qv' i
  , isPropPath (λ {i} → isPropQuot {w = quot-sound qv qv' i}) qv qv' i
isPropScvB {n} {X} {Pi A B} {tmsacc acc} {f} sf sf' i a v sv = let
  (b , ab , sb) = sf a v sv
  (b' , ab' , sb') = sf' a v sv
  ap = applySound ab ab'
  in hmerge ap i
   , isPropPath (λ {i} → isPropApply {v = hmerge ap i}) ab ab' i
   , isPropPath (λ {i} → isPropScvB {v = hmerge ap i}) sb sb' i
   
isPropScvA : {X : Con} {A : Σ (TyS n X) TmsAcc} {v : Val n X ⌜ A ⌝TySAcc} → isProp (scvA A v)
isPropScvA {n} {X} {A} {v} = isPropScvB

abstract
  isPropScv : {X : Con} {A : Ty n X} {v : Val n X A} → isProp (scv A v)
  isPropScv {n} {X} {A} {v} = transport (λ i → {A : TySAcc≡Ty {n} {X} i} {v : Val n X (TySAcc≡Ty-Ty i A)} → isProp (scvA≡scv i A v)) isPropScvA {A} {v}

  isPropSce : {X Y : Con} {p : Env X Y} → isProp (sce p)
  isPropSce {X} {∅} {p} tt tt = refl
  isPropSce {X} {Y , A} {env (p , x)} (scp , scx) (scp' , scx') = cong₂ {C = λ _ _ → sce p × scv _ x} (_,_) (isPropSce scp scp') (isPropScv {v = x} scx scx')


scvB-quot : {n : ℕ} {X : Con} {A : TyS n X} {acc : TmsAcc A}
        → {v : Val n X ⌜ A ⌝TyS} → scvB A acc v
        → Σ[ n ∈ Nf n X ⌜ A ⌝TyS ] quot v n

scvB-unquot : {n : ℕ} {X : Con} {A : TyS n X} {acc : TmsAcc A}
          → {v : Sus n X ⌜ A ⌝TyS} → (w : Nu n X ⌜ A ⌝TyS) → quots v w
          → scvB A acc (neu v)

scvB-var : {n : ℕ} {X : Con} {A : TyS n X} {acc : TmsAcc A} {x : In n X ⌜ A ⌝TyS} → scvB A acc (neu (var x))
scvB-var {A = A} {x = x} = scvB-unquot (var x) quotsvar

abstract
  TyS[wk] : {n : ℕ} {X : Con} {A : TyS n X}
          → ⌜ A ⌝TyS [ wk {A = ⌜ A ⌝TyS} ]T ≡ ⌜ A [ ⌜ weakener ⌜ A ⌝TyS idwk ⌝Wk ]TyS ⌝TyS
  TyS[wk] {A = A} = ⌜ A ⌝TyS [ wk ]T
                    ≡⟨ idwk-lemma ⟩
                    ⌜ A ⌝TyS [ ⌜ weakener ⌜ A ⌝TyS idwk ⌝Wk ]T
                    ≡⟨ sym ⌜[]TyS⌝ ⟩
                    ⌜ A [ ⌜ weakener ⌜ A ⌝TyS idwk ⌝Wk ]TyS ⌝TyS ∎
                    
  ⌜weakener-idwk⌝ : {X : Con} {A : Ty n X}
                 → ⌜ weakener A idwk ⌝Wk ≡ wk {A = A}
  ⌜weakener-idwk⌝ {A = A} = ⌜ weakener A idwk ⌝Wk
                           ≡⟨ ⌜weakener⌝ ⟩
                           ⌜ idwk ⌝Wk ∘t wk
                           ≡⟨ cong (_∘t wk) ⌜idwk⌝ ⟩
                           idt ∘t wk
                           ≡⟨ id∘ ⟩
                           wk ∎

scvB-quot {.(suc n)} {X} {U n} {acc} {v} sv = sv
scvB-quot {n} {X} {El x} {acc} {v} sv = sv
scvB-quot {n} {X} {Pi A B} {tmsacc acc} {f} sf = let
  varz : In n (X , ⌜ A ⌝TyS) (⌜ A [ ⌜ weakener _ idwk ⌝Wk ]TyS ⌝TyS)
  varz = subst (In _ _) TyS[wk] Zero
  wk = ⌜ weakener ⌜ A ⌝TyS idwk ⌝Wk , ⌜ subst (Val _ _) (⌜[]TySAcc⌝ {A = A , tmswf A}) (neu (var varz)) ⌝Val
  (fz , afz , sfz) = sf (weakener _ idwk) (neu (var varz)) (scvB-var {x = varz})
  (nfz , qfz) = scvB-quot {A = B [ wk ]TyS}
                          {acc = acc (B [ wk ]TyS) (π₁ wk) (Pi1 refl)}
                          {v = fz}
                          sfz
  P : ⌜ subst (Val _ _) (⌜[]TySAcc⌝ {A = A , tmswf A}) (neu (var varz)) ⌝Val ⟦ Tm _ _ ⟧ vz
  P = ⌜ subst (Val _ _) (⌜[]TySAcc⌝ {A = A , tmswf A}) (neu (var varz)) ⌝Val
      ⟮ ‼ dcong (⌜_⌝Val) (sym (subst-filler (Val _ _) (⌜[]TySAcc⌝ {A = A , tmswf A}) (neu (var varz)))) ⟯
      ⌜ subst (In _ _) TyS[wk] Zero ⌝In
      ⟮ ‼ dcong (⌜_⌝In) (sym (subst-filler (In _ _) TyS[wk] Zero)) ⟯
      vz □
  BP : ⌜ B [ ⌜ weakener ⌜ A ⌝TyS idwk ⌝Wk , ⌜ subst (Val _ _) (⌜[]TySAcc⌝ {A = A , tmswf A}) (neu (var varz)) ⌝Val ]TyS ⌝TyS ≡ ⌜ B ⌝TyS
  BP = dcong₂ (λ x y → ⌜ B [ x , y ]TyS ⌝TyS) ⌜weakener-idwk⌝ (hcollapse P (cong (⌜ A ⌝TyS [_]T) ⌜weakener-idwk⌝))
     ∙ cong (λ i → ⌜ B [ i ]TyS ⌝TyS) πη ∙ cong ⌜_⌝TyS TyS[id]
  A1 = subst (Val n (X , ⌜ A ⌝TyS)) Pi[] (f [ weakener ⌜ A ⌝TyS idwk ]Val)
  VP1 = tr (Val n (X , ⌜ A ⌝TyS)) idwk-lemma (neu (var Zero))
  VP : subst (Val n (X , ⌜ A ⌝TyS)) (⌜[]TySAcc⌝ {A = A , tmswf A}) (neu (var (subst (In n (X , ⌜ A ⌝TyS)) TyS[wk] Zero))) ⟦ Val _ _ ⟧ VP1
  VP = subst (Val _ _) (⌜[]TySAcc⌝ {A = A , tmswf A}) (neu (var (subst (In n (X , ⌜ A ⌝TyS)) TyS[wk] Zero)))
       ⟮ ‼ sym (subst-filler (Val _ _) (⌜[]TySAcc⌝ {A = A , tmswf A}) (neu (var (subst (In n (X , ⌜ A ⌝TyS)) TyS[wk] Zero)))) ⟯
       neu (var (subst (In n (X , ⌜ A ⌝TyS)) TyS[wk] Zero))
       ⟮ ‼ dcong (λ i → Val.neu (var i)) (sym (subst-filler (In n _) TyS[wk] Zero)) ⟯
       neu (var Zero)
       ⟮ ‼ trfill (Val _ _) idwk-lemma (neu (var Zero)) ⟯
       VP1 □
  afz' : apply A1 VP1 (subst (Val _ _) BP fz)
  afz' = transport (λ i → apply A1 (hmerge VP i) (subst-filler (Val _ _) BP fz i)) afz
  in lam (subst (Nf _ _) BP nfz) , quotPi afz' (transport (λ i → quot (subst-filler (Val _ _) BP fz i) (subst-filler (Nf _ _) BP nfz i)) qfz)

scvB-unquot {.(suc n)} {X} {U n} {acc} {v} w qv = neuU w , quotU qv
scvB-unquot {n} {X} {El u} {acc} {v} w qv = neuEl w , quotEl qv
scvB-unquot {n} {X} {Pi A B} {tmsacc acc} {f} fn qf {Y} a v sv = let
  (m , qm) = scvB-quot sv
  f+ : Sus n Y (Pi (⌜ A ⌝TyS [ ⌜ a ⌝Wk ]T) (⌜ B ⌝TyS [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyS ]T))
  f+ = subst (Sus _ _) Pi[] (f [ a ]Sus)
  v' : Val n Y (⌜ A ⌝TyS [ ⌜ a ⌝Wk ]T)
  v' = subst (Val _ _) ⌜[]TyS⌝ v
  fv : Sus n Y ((⌜ B ⌝TyS [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyS ]T) [ < ⌜ v' ⌝Val > ]T)
  fv = Sus.app f+ v'
  afv = apply.neu {sv = f+} {v = v'}
  nf+≡ : (neu f+) ⟦ Val _ _ ⟧ (subst (Val n Y) Pi[] (neu (f [ a ]Sus)))
  nf+≡ = neu (subst (Sus _ _) Pi[] (f [ a ]Sus))
         ⟮ ‼ dcong Val.neu (sym (subst-filler (Sus _ _) Pi[] (f [ a ]Sus))) ⟯
         neu (f [ a ]Sus)
         ⟮ ‼ subst-filler (Val n Y) Pi[] (neu (f [ a ]Sus)) ⟯
         (subst (Val n Y) Pi[] (neu (f [ a ]Sus))) □
  afv' : apply (subst (Val n Y) Pi[] (neu (f [ a ]Sus)))
               (subst (Val n Y) (⌜[]TySAcc⌝ {A = A , tmswf A}) v)
               (neu (subst (Sus n Y) (hmerge B0≡B1) fv))
  afv' = transport (λ i → apply (hmerge nf+≡ i)
                                 (hmerge []TyS→Acc i)
                                 (neu (subst-filler (Sus n Y) (hmerge B0≡B1) fv i))) afv
  qm' = transport (λ i → quot (subst-filler (Val n Y) ⌜[]TyS⌝ v i)
                               (subst-filler (Nf n Y) ⌜[]TyS⌝ m i)) qm
  FM : (⌜ B ⌝TyS [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyS ]T [ < ⌜ subst (Nf n Y) ⌜[]TyS⌝ m ⌝Nf > ]T) ⟦ Ty _ ⟧ ⌜ B [ WK1 ]TyS ⌝TyS
  FM = ⌜ B ⌝TyS [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyS ]T [ < ⌜ subst (Nf n Y) ⌜[]TyS⌝ m ⌝Nf > ]T
       ⟮ ‼ cong (λ i → ⌜ B ⌝TyS [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyS ]T [ < i > ]T) (sym (quot≡ qm')) ⟯
       ⌜ B ⌝TyS [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyS ]T [ < ⌜ subst (Val n Y) ⌜[]TyS⌝ v ⌝Val > ]T
       ⟮ B0≡B1 ⟯
       B1 □
  fm : Nu n Y (⌜ B ⌝TyS [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyS ]T [ < ⌜ subst (Nf n Y) ⌜[]TyS⌝ m ⌝Nf > ]T)
  fm = Nu.app (subst (Nu _ _) Pi[] (fn [ a ]Nu)) (subst (Nf _ _) ⌜[]TyS⌝ m)
  fm' = tr (λ x → Nu n Y ((⌜ B ⌝TyS [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyS ]T [ < x > ]T))) (sym (quot≡ qm')) fm
  fm'' : Nu n Y ⌜ B [ WK1 ]TyS ⌝TyS
  fm'' = subst (Nu n Y) (hmerge FM) fm
  fm'≡fm'' : fm' ⟦ Nu _ _ ⟧ fm''
  fm'≡fm'' = fm'
             ⟮ ‼ sym (trfill (λ x → Nu n Y ((⌜ B ⌝TyS [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyS ]T [ < x > ]T))) (sym (quot≡ qm')) fm) ⟯
             fm
             ⟮ ‼ subst-fill (Nu n Y) (hmerge FM) fm ⟯
             fm'' □
  qf+' = transport (λ i → quots (subst-filler (Sus n Y) Pi[] (f [ a ]Sus) i)
                                 (subst-filler (Nu n Y) Pi[] (fn [ a ]Nu) i)) (qf [ a ]quots)
  
  qfv : quots fv fm'
  qfv = quotsapp qf+' qm'
  qfv' : quots (subst (Sus n Y) (hmerge B0≡B1) fv) fm''
  qfv' = transport (λ i → quots (subst-filler (Sus n Y) (hmerge B0≡B1) fv i)
                                 (hcollapse fm'≡fm'' (hmerge B0≡B1) i)) qfv
  in Val.neu (subst (Sus n Y) (hmerge B0≡B1) fv)
   , afv'
   , scvB-unquot fm'' qfv'
  where B0 = ((⌜ B ⌝TyS [ ⌜ a ⌝Wk ↑ ⌜ A ⌝TyS ]T) [ < ⌜ subst (Val n Y) ⌜[]TyS⌝ v ⌝Val > ]T)
        WK1 = ⌜ a ⌝Wk , ⌜ subst (Val n Y) (⌜[]TySAcc⌝ {A = A , tmswf A}) v ⌝Val
        B1 = ⌜ (B [ WK1 ]TyS) , acc (B [ WK1 ]TyS) (π₁ WK1) (Pi1 refl) ⌝TySAcc
        abstract []TyS→Acc : subst (Val n Y) ⌜[]TyS⌝ v ⟦ Val _ _ ⟧ subst (Val n Y) (⌜[]TySAcc⌝ {A = A , tmswf A}) v
                 []TyS→Acc = ‼ (sym (subst-filler (Val n Y) ⌜[]TyS⌝ v))
                            ● ‼ subst-filler (Val n Y) (⌜[]TySAcc⌝ {A = A , tmswf A}) v
                 B0≡B1 : B0 ⟦ Ty _ ⟧ B1
                 B0≡B1 = B0
                         ⟮ ‼ sym [∘]T ⟯
                         ⌜ B ⌝TyS [ (⌜ a ⌝Wk ↑ ⌜ A ⌝TyS) ∘t < ⌜ subst (Val n Y) ⌜[]TyS⌝ v ⌝Val > ]T
                         ⟮ ‼ cong (⌜ B ⌝TyS [_]T) (↑∘<> {u = ⌜ subst (Val n Y) ⌜[]TyS⌝ v ⌝Val})  ⟯
                         ⌜ B ⌝TyS [ ⌜ a ⌝Wk , ⌜ subst (Val n Y) ⌜[]TyS⌝ v ⌝Val ]T
                         ⟮ ‼ cong (λ i → ⌜ B ⌝TyS [ ⌜ a ⌝Wk , ⌜ i ⌝Val ]T) (hmerge []TyS→Acc) ⟯
                         ⌜ B ⌝TyS [ WK1 ]T
                         ⟮ ‼ sym ⌜[]TyS⌝ ⟯
                         ⌜ B [ WK1 ]TyS ⌝TyS □

scvA-quot : {n : ℕ} {X : Con} {A : Σ (TyS n X) TmsAcc}
        → {v : Val n X ⌜ A ⌝TySAcc} → scvA A v
        → Σ[ n ∈ Nf n X ⌜ A ⌝TySAcc ] quot v n
scvA-quot {A = A} {v} sv = scvB-quot sv

scvA-unquot : {n : ℕ} {X : Con} {A : Σ (TyS n X) TmsAcc}
          → {v : Sus n X ⌜ A ⌝TySAcc} → (w : Nu n X ⌜ A ⌝TySAcc) → quots v w
          → scvA A (neu v)
scvA-unquot {A = A} {v} w qv = scvB-unquot w qv

abstract
  scv-quot : {n : ℕ} {X : Con} {A : Ty n X}
          → {v : Val n X A} → scv _ v
          → Σ[ n ∈ Nf n X A ] quot v n
  scv-quot {n} {X} = transport (λ i → {A : TySAcc≡Ty {n} {X} i}
                                    → {v : Val n X (TySAcc≡Ty-Ty i A)} → scvA≡scv i A v
                                    → Σ[ n ∈ Nf n X (TySAcc≡Ty-Ty i A) ] quot v n) scvA-quot

  scv-unquot : {n : ℕ} {X : Con} {A : Ty n X}
            → {v : Sus n X A} → (w : Nu n X A) → quots v w
            → scv _ (neu v)
  scv-unquot {n} {X} = transport (λ i → {A : TySAcc≡Ty {n} {X} i}
                                      → {v : Sus n X (TySAcc≡Ty-Ty i A)}
                                      → (w : Nu n X (TySAcc≡Ty-Ty i A))
                                      → quots v w
                                      → scvA≡scv i A (neu v)) scvA-unquot

scv-id : {X : Con} {A : Ty n X} {x : In n X A} → scv A (neu (var x))
scv-id {x = x} = scv-unquot (var x) quotsvar

sce-idenv : (X : Con) → sce (idenv {X})
sce-idenv ∅ = tt
sce-idenv (X , A) = sce-idenv X [ weakener _ idwk ]sce , transport (λ i → scv _ (trfill (Val _ _) ([⌜id[E]⌝] {A = A}) (neu (var Zero)) i)) scv-id

isPropEvalScv : {X Y : Con} {A : Ty n Y} {u : Tm n Y A} {p : Env X Y}
             → isProp (Σ[ B ∈ Ty n X ] Σ[ v ∈ Val n X B ] eval u p v × scv _ v)

isPropEvalsSce : {X Y Z : Con} {s : Tms Y Z} {p : Env X Y}
             → isProp (Σ[ v ∈ Env X Z ] evals s p v × sce v)

isPropEvalScv {n} {X} {Y} {A} {u} {p} (B , x , ex , sx) (B' , x' , ex' , sx') i
  = type (evalSound ex ex') i
  , path (evalSound ex ex') i
  , isPropPath {B = λ i → eval u p (path (evalSound ex ex') i)} isPropEval ex ex' i
  , isPropPath {B = λ i → scv _ (path (evalSound ex ex') i)} isPropScv sx sx' i

isPropEvalsSce {X} {Y} {Z} {s} {p} (v , es , sv) (v' , es' , sv') i
  = evalsSound es es' i
  , isPropPath {B = λ i → evals s p (evalsSound es es' i)} isPropEvals es es' i
  , isPropPath {B = λ i → sce (evalsSound es es' i)} isPropSce sv sv' i
