open import Prelude
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Data.Sigma.Properties
open import Cubical.Functions.FunExtEquiv using (funExtDep)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path

open import Cubical.Reflection.StrictEquiv

import IndexedContainer as ICModule
import IndexedMonad as IMModule

module IndexedMonadMorphism
  {I : Type} 
  (T T′ : ICModule.IndexedContainer I) 
  (f : ICModule._⇒_ I T T′)
  where

open import Definitions I
open ICModule I
open import IndexedContainer.MonoidalCategory 
open import IndexedContainer.Properties

open Fibration

open IndexedContainer T
open IndexedContainer T′ renaming (S to S′; P to P′)

private
  σf = σ f
  πf = π f
  
module _
  (ICMon-T : IMModule.ICMonoid I T)
  (ICMon-T′ : IMModule.ICMonoid I T′)
  where

  open IMModule.RawICMonoid (ICMon-T .fst)
  open IMModule.RawICMonoid (ICMon-T′ .fst) renaming (η to η′; μ to μ′)

  record isICMonoidMorphism : Type where
    field
      hom-η : η ; f ≡ η′
      hom-μ : f ⊗₁ f ; μ′ ≡ μ ; f 
    
module _
  (ICMS-T : IMModule.ICMS I T)
  (ICMS-T′ : IMModule.ICMS I T′)
  where

  private
    module raw = IMModule.RawICMS (ICMS-T .fst)
    module raw′ = IMModule.RawICMS (ICMS-T′ .fst)

  record isICMM : Type where
    field
      f-e : ∀ {i : I} 
        → σf i (raw.e i) ≡ raw′.e i

      f-P-e-idx : ∀ {i j : I}
        → PathP (λ ι → P′ {i} (f-e ι) j → i ≡ j)
          (πf (raw.e i) » raw.P-e-idx) 
          raw′.P-e-idx

      f-• : ∀ {i : I} (s : S i) (v : ∀ {j : I} → P s j → S j) 
        → σf i s raw′.• (λ {j} → πf s » v » σf j) ≡ σf i (s raw.• v)
      
      f-↑-PathP : 
        ∀ {i : I} 
        {s : S i} 
        {v : ∀ {j : I} → P s j → S j} 
        {j : I}
        → PathP (λ ι → P′ (f-• s v ι) j → I)
          (_ raw′.↑_)
          (πf _ » _ raw.↑_)

      f-↖-PathP : 
        ∀ {i : I} 
        {s : S i} 
        {v : ∀ {j : I} → P s j → S j} 
        {j : I}
        → PathP (λ ι → (p : P′ (f-• s v ι) j) → P s (f-↑-PathP ι p))
          (_ raw′.↖_ » πf _)
          (πf _ » _ raw.↖_)

      f-↗-PathP : 
        ∀ {i : I} 
        {s : S i} 
        {v : ∀ {j : I} → P s j → S j} 
        {j : I}
        → PathP (λ ι → (p : P′ (f-• s v ι) j) → P (v (f-↖-PathP ι p)) j)
          (_ raw′.↗_ » πf _)
          (πf _ » _ raw.↗_)

module _ 
  {ICMS-T : IMModule.ICMS I T}
  {ICMS-T′ : IMModule.ICMS I T′}
  (isicmm : isICMM ICMS-T ICMS-T′)
  where

  private
    module raw = IMModule.RawICMS (ICMS-T .fst)
    module raw′ = IMModule.RawICMS (ICMS-T′ .fst)

  open IMModule I
  open isICMonoidMorphism
  open isICMM isicmm

  isICMM→isICMonoidMorphism : isICMonoidMorphism (ICMS→ICMonoid _ ICMS-T) (ICMS→ICMonoid _ ICMS-T′)
  isICMM→isICMonoidMorphism .hom-η = ⇒PathP λ i _ → ΣPathP
    ( f-e
    , implicitFunExt f-P-e-idx
    )
  isICMM→isICMonoidMorphism .hom-μ = ⇒PathP λ { i (s , v) → ΣPathP
      ( f-• s v  
      , implicitFunExt λ {_} → congPathEquiv (λ ι → invEquiv Σ-Π-≃) .fst
        (ΣPathP
          ( f-↑-PathP 
          , congPathEquiv (λ ι → invEquiv Σ-Π-≃) .fst
            (ΣPathP 
              ( f-↖-PathP 
              , f-↗-PathP
              )
            )
          )
        )
      )
    }

module _ 
  {ICMon-T : IMModule.ICMonoid I T}
  {ICMon-T′ : IMModule.ICMonoid I T′}
  (isicmonmor : isICMonoidMorphism ICMon-T ICMon-T′)
  where

  private
    module raw = IMModule.RawICMonoid (ICMon-T .fst)
    module raw′ = IMModule.RawICMonoid (ICMon-T′ .fst)

  open IMModule I
  open isICMonoidMorphism isicmonmor
  open isICMM 

  isICMonoidMorphism→isICMM : isICMM (ICMonoid→ICMS _ ICMon-T) (ICMonoid→ICMS _ ICMon-T′)
  isICMonoidMorphism→isICMM .f-e ι = σ (hom-η ι) _ _ 
  isICMonoidMorphism→isICMM .f-P-e-idx ι p = π (hom-η ι) _ p
  isICMonoidMorphism→isICMM .f-• s v ι = σ (hom-μ ι) _ (s , v)
  isICMonoidMorphism→isICMM .f-↑-PathP ι p′ = π (hom-μ ι) _ p′ .fst
  isICMonoidMorphism→isICMM .f-↖-PathP ι p′ = π (hom-μ ι) _ p′ .snd .fst
  isICMonoidMorphism→isICMM .f-↗-PathP ι p′ = π (hom-μ ι) _ p′ .snd .snd

module _ 
  {ICMon-T : IMModule.ICMonoid I T}
  {ICMon-T′ : IMModule.ICMonoid I T′}
  where

  open IMModule I

  isICMonoidMorphism≃isICMM : isICMonoidMorphism ICMon-T ICMon-T′ ≃ isICMM (ICMonoid→ICMS _ ICMon-T) (ICMonoid→ICMS _ ICMon-T′)
  unquoteDef isICMonoidMorphism≃isICMM = 
    defStrictEquiv 
      isICMonoidMorphism≃isICMM 
      isICMonoidMorphism→isICMM   
      isICMM→isICMonoidMorphism
