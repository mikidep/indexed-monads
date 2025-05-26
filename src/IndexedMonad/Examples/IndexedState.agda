open import Prelude

module IndexedMonad.Examples.IndexedState (I : Type) (E : I → Type) (issI : isSet I) where

open import IndexedContainer I
open IndexedContainer

-- ∀ i → E i → Σ j . E j × X j
StateIC : IndexedContainer
StateIC .S i = E i → Σ I E
StateIC .P {i} ms j = Σ (E i) (λ ei → ms ei .fst ≡ j) 

open import IndexedMonad I StateIC 
open RawICMS

stateic-raw-icms : RawICMS
stateic-raw-icms .e i ei = i , ei
stateic-raw-icms ._•_ ms ms′ ei = ms′ (ei , refl) (ms ei .snd)
stateic-raw-icms .↑ {s = ms} (ei , _) = ms ei .fst
stateic-raw-icms .↖ (ei , _) = ei , refl
stateic-raw-icms .↗ {s = ms} (ei , eq) = ms ei .snd , eq
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

