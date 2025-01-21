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

module IndexedState (I : Type) (E : I → Type) (issI : isSet I) where
  open IC I
  open IndexedContainer

  -- ∀ i → E i → Σ j . E j × X j
  StateIC : IndexedContainer
  StateIC .S i = E i → Σ I E
  StateIC .P {i} ms j = Σ (E i) (λ ei → ms ei .fst ≡ j) 

  open IM I StateIC 
  open RawICMS

  stateic-raw-icms : RawICMS
  stateic-raw-icms .e i ei = i , ei
  stateic-raw-icms ._•_ ms ms′ ei = ms′ (ei , refl) (ms ei .snd)
  stateic-raw-icms ._↑_ {s = ms} _ (ei , _) = ms ei .fst
  stateic-raw-icms ._↖_ _ (ei , _) = ei , refl
  stateic-raw-icms ._↗_ {s = ms} _ (ei , eq) = ms ei .snd , eq
  stateic-raw-icms .P-e-idx = snd

  open isICMS
  open import Cubical.Data.Sigma using (ΣPathP)
  open import Cubical.Foundations.Transport
  open import Cubical.Foundations.Path

  stateic-is-icms : isICMS stateic-raw-icms
  stateic-is-icms .e-unit-l ms = refl
  stateic-is-icms .↖-unit-l {i = i} ms {j = j} = 
    funExt λ {
      (ei , eq) → ΣPathP ( substRefl {B = E} ei , toPathP (issI _ _ _ _))
    }
  stateic-is-icms .e-unit-r ms = substRefl {B = λ i → E i → Σ I E} ms
  stateic-is-icms .↗-unit-r {i = i} ms {j = j} = toPathP (funExt λ {(ei , eq) → ΣPathP
    ( substRefl {B = E} _ ∙ substRefl {B = E} _ ∙ substRefl {B = E} ei
    , toPathP (issI _ _ _ _)
    ) })
  stateic-is-icms .•-assoc ms ms′ ms″ = refl
  stateic-is-icms .↑-↗↑-assoc ms ms′ ms″ = refl
  stateic-is-icms .↖↑-↑-assoc ms ms′ ms″ = refl
  stateic-is-icms .↖↖-↖-assoc ms ms′ ms″ = refl
  stateic-is-icms .↖↗-↗↖-assoc ms ms′ ms″ = refl
  stateic-is-icms .↗-↗↗-assoc ms ms′ ms″ = refl

module NonIndexedState (E : Type) where
  open import Cubical.Data.Unit.Properties using (isSetUnit)
  open IndexedState Unit (λ _ → E) isSetUnit renaming (StateIC to StateC)

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
  StateCIso .Iso.fun (s , px) e = s e .snd , px (e , refl)
  StateCIso .Iso.inv sx = sx » fst » (tt ,_) , fst » sx » snd
  StateCIso .Iso.rightInv sx = refl
  StateCIso .Iso.leftInv scx = refl

