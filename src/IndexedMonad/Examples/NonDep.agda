open import Prelude
open import Cubical.Data.Unit

module IndexedMonad.Examples.NonDep (S P : Type) where

open import IndexedContainer Unit
open import IndexedMonad Unit (const S ⊲ λ _ _ → P)

module _
  (e : S)
  (_•_ : S → (P → S) → S)
  where

  raw : RawICMS
  raw .RawICMS.e = const e
  raw .RawICMS._•_ s v = s • v
  raw .RawICMS.↑ = {! !}
  raw .RawICMS.↖ = {! !}
  raw .RawICMS.↗ = {! !}
  raw .RawICMS.P-e-idx = λ _ → refl

  open isICMS
  isicms : isICMS raw
  isicms .e-unit-l s = {! !}
  isicms .↖-unit-l s = funExt {! !}
  isicms .e-unit-r = {! !}
  isicms .↗-unit-r = {! !}
  isicms .•-assoc = {! !}
  isicms .↑-↗↑-assoc = {! !}
  isicms .↖↑-↑-assoc = {! !}
  isicms .↖↖-↖-assoc = {! !}
  isicms .↖↗-↗↖-assoc = {! !}
  isicms .↗-↗↗-assoc = {! !}


