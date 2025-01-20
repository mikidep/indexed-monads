open import Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Fin as Fin using (Fin)

module IndexedMonad.Examples where

import IndexedContainer as IC
import IndexedMonad as IM

module ProductMonad {I : Type}
  (T T′    : IC.IndexedContainer I)
  (icms-T  : IM.ICMS I T)
  (icms-T′ : IM.ICMS I T′)
  where

  open IC
  open IM

  open IndexedContainer
  open ICMS

  open import Cubical.Data.Sigma using (_×_)
  open import Cubical.Data.Sum as Sum using (_⊎_; inl; inr)

  T×T′ : IndexedContainer I
  T×T′ .S i = T .S i × T′ .S i
  T×T′ .P (s , s′) j = T .P s j ⊎ T′ .P s′ j

  open RawICMS (icms-T .icms)
  open RawICMS (icms-T′ .icms) using () renaming
    ( e to e′
    ; _•_ to _•′_ 
    ; _↑_ to _↑′_
    ; _↖_ to _↖′_
    ; _↗_ to _↗′_
    ; P-e-idx to P-e-idx′
    )

  module _ {A B C D : Type} where
    l : (A ⊎ C → B × D) → A → B 
    l f = inl » f » fst 

    r : (A ⊎ C → B × D) → C → D 
    r f = inr » f » snd 

  raw-icms-T×T′ : RawICMS I T×T′
  raw-icms-T×T′ .RawICMS.e i = e i , e′ i
  raw-icms-T×T′ .RawICMS._•_ (s , s′) vv′ = s • l vv′ , s′ •′ r vv′
  raw-icms-T×T′ .RawICMS._↑_ vv′ = Sum.rec (l vv′ ↑_) (r vv′ ↑′_)
  raw-icms-T×T′ .RawICMS._↖_ vv′ =
    Sum.elim
      (λ p → inl (l vv′ ↖ p))
      (λ p → inr (r vv′ ↖′ p))
  raw-icms-T×T′ .RawICMS._↗_ vv′ =
    Sum.elim
      (λ p → inl (l vv′ ↗ p))
      (λ p → inr (r vv′ ↗′ p))
  raw-icms-T×T′ .RawICMS.P-e-idx = Sum.elim P-e-idx P-e-idx′

  open import Cubical.Data.Sigma using (ΣPathP)
  open isICMS
  is = icms-T .is-icms
  is′ = icms-T′ .is-icms

  is-icms-T×T′ : isICMS _ _ raw-icms-T×T′
  is-icms-T×T′ .isICMS.e-unit-l (s , s′) = ΣPathP (is .e-unit-l s , is′ .e-unit-l s′)
  is-icms-T×T′ .isICMS.↖-unit-l (s , s′) ι (inl p) = inl (is .↖-unit-l s ι p)
  is-icms-T×T′ .isICMS.↖-unit-l (s , s′) ι (inr p) = inr (is′ .↖-unit-l s′ ι p)
  is-icms-T×T′ .isICMS.e-unit-r (s , s′) = ΣPathP (is .e-unit-r s , is′ .e-unit-r s′)
  is-icms-T×T′ .isICMS.↗-unit-r (s , s′) ι (inl p) = inl (is .↗-unit-r s ι p)
  is-icms-T×T′ .isICMS.↗-unit-r (s , s′) ι (inr p) = inr (is′ .↗-unit-r s′ ι p)
  is-icms-T×T′ .isICMS.•-assoc ss ss′ ss″ =
    ΣPathP
      ( is .•-assoc (ss .fst) (l ss′) (λ p q → fst (ss″ (inl p) (inl q))) 
      , is′ .•-assoc (ss .snd) (r ss′) (λ p q → snd (ss″ (inr p) (inr q)))  
      )
  is-icms-T×T′ .isICMS.↑-↗↑-assoc ss ss′ ss″ ι (inl p) = is .↑-↗↑-assoc _ _ _ ι p
  is-icms-T×T′ .isICMS.↑-↗↑-assoc ss ss′ ss″ ι (inr p) = is′ .↑-↗↑-assoc _ _ _ ι p
  is-icms-T×T′ .isICMS.↖↑-↑-assoc ss ss′ ss″ ι (inl p) = is .↖↑-↑-assoc _ _ _ ι p
  is-icms-T×T′ .isICMS.↖↑-↑-assoc ss ss′ ss″ ι (inr p) = is′ .↖↑-↑-assoc _ _ _ ι p
  is-icms-T×T′ .isICMS.↖↖-↖-assoc ss ss′ ss″ ι (inl p) = inl (is .↖↖-↖-assoc _ _ _ ι p)
  is-icms-T×T′ .isICMS.↖↖-↖-assoc ss ss′ ss″ ι (inr p) = inr (is′ .↖↖-↖-assoc _ _ _ ι p) 
  is-icms-T×T′ .isICMS.↖↗-↗↖-assoc ss ss′ ss″ ι (inl p) = inl (is .↖↗-↗↖-assoc _ _ _ ι p) 
  is-icms-T×T′ .isICMS.↖↗-↗↖-assoc ss ss′ ss″ ι (inr p) = inr (is′ .↖↗-↗↖-assoc _ _ _ ι p)  
  is-icms-T×T′ .isICMS.↗-↗↗-assoc ss ss′ ss″ ι (inl p) = inl (is  .↗-↗↗-assoc _ _ _ ι p) 
  is-icms-T×T′ .isICMS.↗-↗↗-assoc ss ss′ ss″ ι (inr p) = inr (is′ .↗-↗↗-assoc _ _ _ ι p)  

module IndexedState (I : Type) (E : I → Type) where
  open IC I
  open IndexedContainer

  -- ∀ i → E i → Σ j . E j × X j
  -- ∀ (Σ i . E i) → Σ j . E j × X j
  -- Σ (md : Σ I E → I) (∀ (ms : Σ I E) → E (md ms) × X (md ms))
  -- Σ (md : Σ I E → I) ((∀ (ms : Σ I E) → E (md ms)) × (∀ (ms : Σ I E) → X (md ms)))
  -- Σ (md : Σ I E → I) (∀ (ms : Σ I E) → E (md ms)) × (∀ j (ms : Σ I E) → md ms ≡ j → X j)
  -- Shapes:
  --  Σ (md : Σ I E → I) (∀ (ms : Σ I E) → E (md ms))
  --  ∀ (ms : Σ I E) Σ I E
  StateIC : IndexedContainer
  StateIC .S i = Σ (E i → I) (λ md → (ei : E i) → E (md ei))
  StateIC .P {i} (md , ms) j = Σ (E i) (λ ei → md ei ≡ j)

  open IM I StateIC 
  open RawICMS

  stateic-raw-icms : RawICMS
  stateic-raw-icms .e _ = _ , idfun _
  stateic-raw-icms ._•_ (_ , ms) s′ = _ , λ e → s′ (e , refl) .snd (ms e)
  stateic-raw-icms ._↑_ {s = (md , _)} _ (ei , _) = md ei
  stateic-raw-icms ._↖_ _ (e , _) = e , refl
  stateic-raw-icms ._↗_ {s = (_ , ms)} _ (e , s′e≡) = ms e , s′e≡
  stateic-raw-icms .P-e-idx (_ , i≡j) = i≡j

  open isICMS
  open import Cubical.Data.Sigma using (ΣPathP)
  open import Cubical.Foundations.Transport

  stateic-is-icms : isICMS stateic-raw-icms
  stateic-is-icms .e-unit-l (_ , s) = refl
  stateic-is-icms .↖-unit-l (md , ms) {j} = funExt λ {(e , x) → ΣPathP (substRefl {B = E} e , {!   !})} -- UIP for now
  stateic-is-icms .e-unit-r {i} (md , ms) = 
    ΣPathP
    ( 
      funExt (λ e → transportRefl (md (transport (λ _ → E i) e)) ∙ cong md (transportRefl e))
    , funExt (λ e → {!   !}) -- this is refl on (ms e) up to UIP
    )
  stateic-is-icms .↗-unit-r {i} (md , ms) {j} ι (e , x) = transp (λ _ → E i) ι e , {! !} -- UIP 
  stateic-is-icms .•-assoc s s′ s″ = ΣPathP (refl , funExt λ e → refl)
  stateic-is-icms .↑-↗↑-assoc s s′ s″ = refl
  stateic-is-icms .↖↑-↑-assoc s s′ s″ = refl
  stateic-is-icms .↖↖-↖-assoc s s′ s″ = refl
  stateic-is-icms .↖↗-↗↖-assoc s s′ s″ = refl 
  stateic-is-icms .↗-↗↗-assoc s s′ s″ = refl 

module NonIndexedState (E : Type) where
  open IndexedState Unit (λ _ → E) renaming (StateIC to StateC)

  open IM Unit StateC
  open RawICMS

  statec-raw-icms : RawICMS
  statec-raw-icms .e _ = _ , idfun _
  statec-raw-icms ._•_ s s′ = _ , λ e → s′ (e , refl) .snd (s .snd e)
  statec-raw-icms ._↑_ = _
  statec-raw-icms ._↖_ s′ (e , _) = e , refl
  statec-raw-icms ._↗_ {s = (_ , s)} s′ (e , s′e≡) = s e , s′e≡ 
  statec-raw-icms .P-e-idx (e , i≡j) = i≡j

  open isICMS
  open import Cubical.Data.Sigma using (ΣPathP)

  statec-is-icms : isICMS statec-raw-icms
  statec-is-icms .e-unit-l (_ , s) = refl
  statec-is-icms .↖-unit-l (_ , s) = funExt λ {(e , x) → ΣPathP (substRefl {A = Unit} e , λ ι → x)}
  statec-is-icms .e-unit-r (_ , s) = 
    ΣPathP
    ( refl
    , funExt λ e → 
      substRefl {A = Unit} (s (subst {A = Unit} (λ _ → E) refl e)) 
      ∙ cong s (substRefl {A = Unit} e)
    )
  statec-is-icms .↗-unit-r (_ , s) = funExt λ {(e , x) → ΣPathP (substRefl {A = Unit} e , λ ι → x)}
  statec-is-icms .•-assoc s s′ s″ = ΣPathP (refl , funExt λ e → refl)
  statec-is-icms .↑-↗↑-assoc s s′ s″ = refl
  statec-is-icms .↖↑-↑-assoc s s′ s″ = refl
  statec-is-icms .↖↖-↖-assoc s s′ s″ = refl
  statec-is-icms .↖↗-↗↖-assoc s s′ s″ = refl 
  statec-is-icms .↗-↗↗-assoc s s′ s″ = refl 
  
  open import Cubical.Data.Sigma using (_×_)
  StateF : Type → Type
  StateF X = E → E × X
  State-map : {X Y : Type} → (X → Y) → StateF X → StateF Y
  State-map f sx e = sx e .fst , f (sx e .snd)

  μ : ∀ {X} → StateF (StateF X) → StateF X
  μ ssx = let
      ss = ssx » fst
      sx = ssx » snd
      v = λ (e e′ : E) → sx e e′ .fst
      in λ e → v e (ss e) , snd (snd (ssx e) (fst (ssx e)))
  -- μ ssx = λ e → let (e′ , sx) = ssx e in sx e′

  μ1 = μ {X = Unit}

  μl μr : ∀ {X} → StateF (StateF (StateF X)) → StateF X
  μl = State-map μ » μ
  μr = μ » μ

  assoc : ∀ {X} → μl {X} ≡ μr
  assoc = funExt λ x → refl

  
  open import Cubical.Foundations.Isomorphism
  open IC Unit using (⟦_⟧)

  StateCIso : ∀ {X : Type} → Iso (⟦ StateC ⟧ (λ _ → X) _) (StateF X)
  StateCIso .Iso.fun (s , px) e = s .snd e , px (e , refl)
  StateCIso .Iso.inv sx = (_ , sx » fst) ,  fst » sx » snd 
  StateCIso .Iso.rightInv sx = refl
  StateCIso .Iso.leftInv scx = refl

