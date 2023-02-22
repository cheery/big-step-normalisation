{-# OPTIONS --cubical #-}
module Evaluator where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
--open import Cubical.Foundations.HLevels
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
open import TermInfo
open import EvaluatorSC

private variable n : ℕ

abstract
  tyev∙[]TyP : {X Y : Con} {A : Ty n Y} {p : Tms X Y} → A [ p ]T ≡ ⌜ ev A [ p ]TyP ⌝TyP
  tyev∙[]TyP {p = p} = cong (_[ p ]T) tyev ∙ sym ⌜[]TyP⌝
  
scvPi-intro : {Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {f : Val n Y (Pi A B)}
           → ({X : Con} (a : Wk X Y) {v : Val n X (A [ ⌜ a ⌝Wk ]T)} → scv v
           → Σ[ C ∈ Ty n X ] Σ[ fv ∈ Val n X C ] apply (subst (Val _ _) Pi[] (f [ a ]Val)) v fv × scv fv)
           → scv f
scvPi-intro {n} {Y} {A} {B} {f} fn a v sv with fn a {subst (Val _ _) (sym tyev∙[]TyP) v} sv'
  where P : v ⟦ Val _ _ ⟧ (subst (Val _ _) tyev (subst (Val _ _) (sym (tyev∙[]TyP {A = A} {p = ⌜ a ⌝Wk})) v))
        sv' = transport (λ i → scvP (hcollapse P (dcong ⌜_⌝TyP (path ⌜[]ev⌝)) i)) sv
... | (C , w , afw , sw) = {!evsk!} , {!!} , {!!} , {!!}
  where v' = subst (Val _ _) (sym tyev∙[]TyP) v
        C≡B' : C ≡ B [ ⌜ a ⌝Wk ↑ A ]T [ < ⌜ v' ⌝Val > ]T
        C≡B' = sym (type (apply≡ afw))
        skC≡skB : evsk C ≡ evsk B
        skC≡skB = {!dcong evsk C≡B'!}

scvPi-elim : {Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {f : Val n Y (Pi A B)} → scv f
          → {X : Con} (a : Wk X Y) {v : Val n X (A [ ⌜ a ⌝Wk ]T)} → scv v
          → Σ[ C ∈ Ty n X ] Σ[ fv ∈ Val _ X C ] (apply (subst (Val _ _) Pi[] (f [ a ]Val)) v fv) × scv fv
scvPi-elim {n} {Y} {A} {B} {f} sf {X} a {v} sv with sf a (subst (Val _ _) tyev∙[]TyP v) sv'
  where abstract
          Q : (subst (Val _ _) tyev v) ⟦ Val _ _ ⟧ subst (Val _ _) tyev∙[]TyP v
          Q = subst (Val _ _) tyev v
              ⟮ ‼ sym (subst-filler (Val _ _) tyev v) ⟯
              v
              ⟮ ‼ subst-filler (Val _ _) tyev∙[]TyP v ⟯
              subst (Val _ _) tyev∙[]TyP v □
          R : ev (A [ ⌜ a ⌝Wk ]T) ⟦ (λ i → TyP i _ _) ⟧ ev A [ ⌜ a ⌝Wk ]TyP
          R = hsym (⌜[]ev⌝ {A = A} {p = ⌜ a ⌝Wk})
        sv' = (transport (λ i → scvP (hcollapse Q (dcong ⌜_⌝TyP (hcollapse R (type R))) i)) sv)
... | (C , w , afv , sw) = ⌜ C ⌝TyP , w , afv' , sw'
  where X1 = (subst (Val _ _) Pi[] (subst (Val n Y) tyev f [ a ]Val))
        X2 = (subst (Val _ _) Pi[] (f [ a ]Val))
        v' = subst (Val _ _) ⌜[]TyP⌝ (subst (Val _ _) tyev∙[]TyP v)
        abstract
          X1≡X2 : X1 ⟦ Val _ _ ⟧ X2
          X1≡X2 = X1
                  ⟮ ‼ sym (subst-filler (Val _ _) Pi[] (subst (Val n Y) tyev f [ a ]Val)) ⟯
                  (subst (Val n Y) tyev f [ a ]Val)
                  ⟮ ‼ dcong (_[ a ]Val) (sym (subst-filler (Val n Y) tyev f)) ⟯
                  f [ a ]Val
                  ⟮ ‼ subst-filler (Val _ _) Pi[] (f [ a ]Val) ⟯
                  X2 □
          v'≡v : v' ⟦ Val _ _ ⟧ v
          v'≡v = v'
                 ⟮ ‼ sym (subst-filler (Val _ _) ⌜[]TyP⌝ (subst (Val _ _) tyev∙[]TyP v)) ⟯
                 (subst (Val n X) tyev∙[]TyP v)
                 ⟮ ‼ sym (subst-filler (Val _ _) tyev∙[]TyP v) ⟯
                 v □
        QS : Σ[ S ∈ TySk ] TyP S n (Y , ⌜ fst (evalT* A) ⌝TyS)
        QS = TyS→TyP (subst (λ i → TyS n (Y , i)) (evalT≡ (snd (evalT* A))) (fst (evalT* B)))
        S1 : ⌜ (subst (λ i → TyP (fst QS) n (Y , ⌜ i ⌝TyS)) TyS→TyP≡ (snd QS)) ⌝TyP ⟦ Ty _ ⟧ B
        S1 = ⌜ (subst (λ i → TyP (fst QS) n (Y , ⌜ i ⌝TyS)) TyS→TyP≡ (snd QS)) ⌝TyP
             ⟮ ‼ dcong ⌜_⌝TyP (sym (subst-filler (λ i → TyP (fst QS) n (Y , ⌜ i ⌝TyS)) TyS→TyP≡ (snd QS))) ⟯
             ⌜ snd QS ⌝TyP
             ⟮ ‼ dcong (λ i → ⌜ snd (TyS→TyP i) ⌝TyP) (sym (subst-filler (λ i → TyS n (Y , i)) (evalT≡ (snd (evalT* A))) (fst (evalT* B)))) ⟯
             ⌜ ev B ⌝TyP
             ⟮ ‼ sym tyev ⟯
             B □
        S : ⌜ (subst (λ i → TyP (fst QS) n (Y , ⌜ i ⌝TyS)) TyS→TyP≡ (snd QS)) ⌝TyP [ ⌜ a ⌝Wk ↑ ⌜ ev A ⌝TyP ]T ⟦ Ty _ ⟧ B [ ⌜ a ⌝Wk ↑ A ]T
        S = pathh (cong (λ i → (X Con., (i [ ⌜ a ⌝Wk ]T))) (sym tyev))
                  (λ k → (hcollapse S1 (cong (Y Con.,_) (sym tyev)) k) term.[ ⌜ a ⌝Wk ↑ (sym (tyev {A = A}) k) ]T)
        afv' : apply X2 v w
        afv' = transport (λ i → apply (hcollapse X1≡X2 (dcong₂ term.Pi (cong (_[ ⌜ a ⌝Wk ]T) (sym tyev)) (hcollapse S (cong (λ i → (X Con., (i [ ⌜ a ⌝Wk ]T))) (sym (tyev))))) i)
                                       (hcollapse v'≡v (cong (_[ ⌜ a ⌝Wk ]T) (sym tyev)) i) w) afv
        sw'' : scvP {A = C} w
        sw'' = sw
        w≡w' : w ⟦ Val _ _ ⟧ subst (Val _ _) tyev w
        w≡w' = ‼ subst-filler (Val _ _) tyev w
        Z : C ⟦ (λ i → TyP i _ _) ⟧ ev ⌜ C ⌝TyP
        Z = evty
        sw' : scvP {A = ev ⌜ C ⌝TyP} (subst (Val _ _) tyev w)
        sw' = transport (λ i → scvP (hcollapse w≡w' (dcong ⌜_⌝TyP (hcollapse Z (type Z))) i)) sw

scv-eval : {X Y : Con} {A : Ty n X}
        → (u : Tm n X A) → (p : Env Y X) → sce p
        → Σ[ B ∈ Ty n Y ] Σ[ v ∈ Val n Y B ] (eval u p v) × scv v
sce-evals : {X Y Z : Con} (p : Tms Y Z) (s : Env X Y) → sce s
         → Σ[ v ∈ Env X Z ] evals p s v × sce v

open import Proposition

scv-evalᴹ : Motives
Motives.Tmsᴹ scv-evalᴹ {Y} {Z} p = {X : Con} (s : Env X Y) → sce s → Σ[ v ∈ Env X Z ] evals p s v × sce v
Motives.Tmᴹ scv-evalᴹ {n} {Y} {A} u = {X : Con} (p : Env X Y) → sce p → Σ[ B ∈ Ty n X ] Σ[ v ∈ Val n X B ] (eval u p v) × scv v
Motives.Tyᴹ scv-evalᴹ A = ⊤

scv-evalᴿ : Methods scv-evalᴹ
Methods._[_]Tᴹ scv-evalᴿ tt _ = tt
Methods.Uᴹ scv-evalᴿ = tt
Methods.Elᴹ scv-evalᴿ _ = tt
Methods.Piᴹ scv-evalᴿ tt tt = tt
Methods.idtᴹ scv-evalᴿ s ss = s , evalsid , ss
Methods._∘tᴹ_ scv-evalᴿ fp fv s ss = let
  (v' , ve , sv) = fv s ss
  (p' , vp' , sp') = fp v' sv
  in p' , evals∘ ve vp' , sp'
Methods.εᴹ scv-evalᴿ s ss = env tt , evalsε , tt
Methods._,ᴹ_ scv-evalᴿ {A = A} {p} {u} fp fu s ss = let
  (p' , p'e , sp') = fp s ss
  (B , u' , u'e , su') = fu s ss
  P : B ≡ A [ ⌜ p' ⌝Env ]T
  P = evals,-aux p'e u'e
  u'' = tr (Val _ _) P u'
  su'' = transport (λ i → scv (trfill (Val _ _) P u' i)) su'
  in env (p' , u'') , evals, p'e u'e , sp' , su''
Methods.π₁ᴹ scv-evalᴿ fp s ss with fp s ss
... | env (p , x) , p'e , (sp , sx) = p , evalsπ₁ p'e , sp
Methods.π₂ᴹ scv-evalᴿ fp s ss with fp s ss
... | (env (p , x) , p'e , (sp , sx)) = _ , x , evalπ₂ p'e , sx
Methods._[_]ᴹ scv-evalᴿ fu fp s ss = let
  (p' , ep , sp') = fp s ss
  (A , x' , ex' , sx') = fu p' sp'
  in _ , x' , eval[] ep ex' , sx'
Methods.lamᴹ scv-evalᴿ {A = A} {B} {u} fu p sp = let
  lup = lam u p
  lup' = subst (Val _ _) Pi[] lup
  slup' : scv lup'
  slup' = scvPi-intro {f = lup'} λ a {v} sv → let
            P : A [ ⌜ p ⌝Env ]T [ ⌜ a ⌝Wk ]T ≡ A [ ⌜ p [ a ]Env ⌝Env ]T
            P = sym [[]Env]
            v' : Val _ _ (A [ ⌜ p [ a ]Env ⌝Env ]T)
            v' = subst (Val _ _) P v
            v≡v' = subst-filler (Val _ _) P v
            sv' : scv v'
            sv' = transport (λ i → scv (v≡v' i)) sv
            (C , upv , eupv , supv) = fu (env (p [ a ]Env , v')) (sp [ a ]sce , sv')
            Q : B [ ⌜ p ⌝Env ↑ A ]T [ ⌜ a ⌝Wk ↑ (A [ ⌜ p ⌝Env ]T) ]T
                ⟦ Ty _ ⟧
                B [ ⌜ p [ a ]Env ⌝Env ↑ A ]T
            Q = B [ ⌜ p ⌝Env ↑ A ]T [ ⌜ a ⌝Wk ↑ (A [ ⌜ p ⌝Env ]T) ]T
                ⟮ ‼ sym [∘]T ⟯
                B [ (⌜ p ⌝Env ↑ A) ∘t (⌜ a ⌝Wk ↑ (A [ ⌜ p ⌝Env ]T)) ]T
                ⟮ hcong (B [_]T) ↑∘↑ ⟯
                B [ (⌜ p ⌝Env ∘t ⌜ a ⌝Wk) ↑ A ]T
                ⟮ ‼ dcong (λ x → B [ x ↑ A ]T) (sym ⌜[]Env⌝) ⟯
                B [ ⌜ p [ a ]Env ⌝Env ↑ A ]T □
            R : Pi (A [ ⌜ p [ a ]Env ⌝Env ]T) (B [ ⌜ p [ a ]Env ⌝Env ↑ A ]T)
                ≡ Pi (A [ ⌜ p ⌝Env ]T [ ⌜ a ⌝Wk ]T) (B [ ⌜ p ⌝Env ↑ A ]T [ ⌜ a ⌝Wk ↑ (A [ ⌜ p ⌝Env ]T) ]T)
            R = λ i → Pi (P (~ i)) (hcollapse Q (cong (_ Con.,_) P) (~ i))
            lup+ = subst (Val _ _) Pi[] (lam u (p [ a ]Env))
            lup+' = subst (Val _ _) Pi[] (subst (Val _ _) Pi[] (lam u p) [ a ]Val)
            lup+≡lup+' : lup+ ⟦ Val _ _ ⟧ lup+'
            lup+≡lup+' = lup+
                         ⟮ ‼ sym (subst-filler (Val _ _) Pi[] (lam u (p [ a ]Env))) ⟯
                         lam u (p [ a ]Env)
                         ⟮ ‼ trfill (Val _ _) [[]Env] (lam u (p [ a ]Env)) ⟯
                         (lam u p [ a ]Val)
                         ⟮ ‼ dcong (_[ a ]Val) (subst-filler (Val _ _) Pi[] (lam u p)) ⟯
                         subst (Val _ _) Pi[] (lam u p) [ a ]Val
                         ⟮ ‼ subst-filler (Val _ _) Pi[] _ ⟯
                         lup+' □
            aupv : apply lup+ v' upv
            aupv = lam eupv
            aupv' = apply lup+' v upv
            aupv' = transport (λ i → apply (hcollapse lup+≡lup+' R i) (v≡v' (~ i)) upv) aupv
            in C , upv , aupv' , supv
         
  slup : scv lup
  slup = transport (λ i → scv (subst-filler (Val _ _) Pi[] lup (~ i))) slup'
  in _ , lup , evallam , slup
Methods.appᴹ scv-evalᴿ {A = A} {B} {f} fx (env (s , v)) (ss , sv) = let
  (C , fp , efp , sfp) = fx s ss
  P : C ≡ Pi (A [ ⌜ s ⌝Env ]T) (B [ ⌜ s ⌝Env ↑ A ]T)
  P = C
      ≡⟨ type (eval≡ efp) ⟩
      Pi A B [ ⌜ s ⌝Env ]T
      ≡⟨ Pi[] ⟩
      Pi (A [ ⌜ s ⌝Env ]T) (B [ ⌜ s ⌝Env ↑ A ]T) ∎
  fp' = subst (Val _ _) P fp
  fp≡fp' = subst-filler (Val _ _) P fp
  efp' = transport (λ i → eval f s (fp≡fp' i)) efp
  sfp' = transport (λ i → scv (fp≡fp' i)) sfp
  Q : A [ ⌜ s ⌝Env ]T ≡ A [ ⌜ s ⌝Env ]T [ ⌜ idwk ⌝Wk ]T
  Q = A [ ⌜ s ⌝Env ]T
      ≡⟨ sym [id]T ⟩
      (A [ ⌜ s ⌝Env ]T) [ idt ]T
      ≡⟨ cong (A [ ⌜ s ⌝Env ]T [_]T) (sym ⌜idwk⌝) ⟩
      (A [ ⌜ s ⌝Env ]T) [ ⌜ idwk ⌝Wk ]T ∎
  v' = subst (Val _ _) Q v
  v≡v' = subst-filler (Val _ _) Q v
  sv' = transport (λ i → scv (v≡v' i)) sv
  D , fpv , afpv , sfpv = scvPi-elim {f = fp'} sfp' idwk {v = v'} sv'
  fp'' = subst (Val _ _) Pi[] (fp' [ idwk ]Val)
  R : B [ ⌜ s ⌝Env ↑ A ]T ⟦ Ty _ ⟧ B [ ⌜ s ⌝Env ↑ A ]T [ ⌜ idwk ⌝Wk ↑ _ ]T
  R = B [ ⌜ s ⌝Env ↑ A ]T
      ⟮ ‼ sym [id]T ⟯
      B [ ⌜ s ⌝Env ↑ A ]T [ idt ]T
      ⟮ hcong (B [ ⌜ s ⌝Env ↑ A ]T [_]T) (hsym ↑id) ⟯
      (B [ ⌜ s ⌝Env ↑ A ]T) [ idt ↑ (A [ ⌜ s ⌝Env ]T) ]T
      ⟮ ‼ dcong (λ x → (B [ ⌜ s ⌝Env ↑ A ]T) [ x ↑ (A [ ⌜ s ⌝Env ]T) ]T) (sym ⌜idwk⌝) ⟯
      (B [ ⌜ s ⌝Env ↑ A ]T) [ ⌜ idwk ⌝Wk ↑ (A [ ⌜ s ⌝Env ]T) ]T □
  Vid : ⌜ fp' [ idwk ]Val ⌝Val ⟦ Tm _ _ ⟧ ⌜ fp' ⌝Val
  Vid = ⌜ fp' [ idwk ]Val ⌝Val
        ⟮ ‼ ⌜[]Val⌝ {v = fp'} ⟯
        ⌜ fp' ⌝Val [ ⌜ idwk ⌝Wk ]
        ⟮ ‼ dcong (⌜ fp' ⌝Val [_]) ⌜idwk⌝ ⟯
        ⌜ fp' ⌝Val [ idt ]
        ⟮ [id] ⟯
        ⌜ fp' ⌝Val □
  [⌜wkid⌝]T : {n : ℕ} {X : Con} {A : Ty n X} → A [ ⌜ idwk ⌝Wk ]T ≡ A
  [⌜wkid⌝]T = λ {n} {X} {A} → cong (A [_]T) ⌜idwk⌝ ∙ [id]T
  fp''≡fp' : fp'' ⟦ Val _ _ ⟧ fp'
  fp''≡fp' = fp''
             ⟮ ‼ sym (subst-filler (Val _ _) Pi[] (fp' [ idwk ]Val)) ⟯
             fp' [ idwk ]Val
             ⟮ ‼ veqPath (hcollapse Vid [⌜wkid⌝]T) ⟯
             fp' □
  afpv' : apply fp' v fpv
  afpv' = transport (λ i → apply (hcollapse fp''≡fp' (cong₂ term.Pi (sym Q) (sym (hcollapse R (cong (_ Con.,_) Q)))) i) (v≡v' (~ i)) fpv) afpv
  in D , fpv , evalapp efp' afpv' , sfpv
Methods.isPropTmsᴹ scv-evalᴿ P Q i s ss = isPropEvalsSce (P s ss) (Q s ss) i
Methods.isPropTmᴹ scv-evalᴿ P Q i p sp = isPropEvalScv (P p sp) (Q p sp) i
Methods.isPropTyᴹ scv-evalᴿ tt tt = refl

scv-eval u p sp = Methods.elimTm scv-evalᴿ u p sp
sce-evals s p sp = Methods.elimTms scv-evalᴿ s p sp

termination : {X : Con} {A : Ty n X} {u : Tm n X A}
            → Σ[ w ∈ Nf n X A ] norm u w
termination {n} {X} {A} {u} = let
  (B , v , ev , sc) = scv-eval u idenv (sce-idenv X)
  (w , q) = scv-quot {v = v} sc
  B≡A : B ≡ A
  B≡A = type (eval≡ ev) ∙ cong (A [_]T) idenv≡ ∙ [id]T
  in subst (Nf n X) B≡A w
   , subst (Val n X) B≡A v
   , transport (λ i → eval u idenv (subst-filler (Val n X) B≡A v i)) ev
   , transport (λ i → quot (subst-filler (Val n X) B≡A v i)
                            (subst-filler (Nf n X) B≡A w i)) q
