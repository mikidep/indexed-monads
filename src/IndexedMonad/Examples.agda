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

  open import Cubical.Data.Sigma using (_×_)
  open import Cubical.Data.Sum as Sum using (_⊎_; inl; inr)

  T×T′ : IndexedContainer I
  T×T′ .S i = T .S i × T′ .S i
  T×T′ .P (s , s′) j = T .P s j ⊎ T′ .P s′ j

  open RawICMS (icms-T .fst)
  open RawICMS (icms-T′ .fst) using () renaming
    ( e to e′
    ; _•_ to _•′_ 
    ; ↑ to ↑′
    ; ↖ to ↖′
    ; ↗ to ↗′
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
  raw-icms-T×T′ .RawICMS.↑ = Sum.rec ↑ ↑′
  raw-icms-T×T′ .RawICMS.↖ = Sum.elim (↖ » inl) (↖′ » inr)
  raw-icms-T×T′ .RawICMS.↗ = Sum.elim (↗ » inl) (↗′ » inr)
  raw-icms-T×T′ .RawICMS.P-e-idx = Sum.elim P-e-idx P-e-idx′

  open import Cubical.Data.Sigma using (ΣPathP)
  open isICMS
  is = icms-T .snd
  is′ = icms-T′ .snd

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

