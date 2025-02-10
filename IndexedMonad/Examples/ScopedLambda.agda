open import Prelude

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Literals
open import IndexedContainer ℕ
open import Definitions ℕ

module IndexedMonad.Examples.ScopedLambda where

open import Cubical.Data.Sum as Sum using (_⊎_; inl; inr)
open IndexedContainer

data LamS (n : ℕ) : Type where
  var :                       LamS n
  app : (M N : LamS n)      → LamS n
  lam : (M : LamS (suc n))  → LamS n

module _ {ℓ} {B : ℕ → Type ℓ}  
  (var* : {n : ℕ} → B n) 
  (app* : {n : ℕ} → B n → B n → B n) 
  (lam* : {n : ℕ} → B (suc n) → B n) where

  LamS-rec : ∀ {n} (s : LamS n) → B n
  LamS-rec var = var*
  LamS-rec (app M N) = app* (LamS-rec M) (LamS-rec N)
  LamS-rec (lam M) = lam* (LamS-rec M)

module _ {ℓ} {B : ∀ {n} → LamS n → Type ℓ}  
  (var* : {n : ℕ} → B {n} var) 
  (app* : {n : ℕ} {M N : LamS n} → B M → B N → B (app M N)) 
  (lam* : {n : ℕ} {M : LamS (suc n)} → B M → B (lam M)) where

  LamS-elim : ∀ {n} (s : LamS n) → B s
  LamS-elim var = var*
  LamS-elim (app M N) = app* (LamS-elim M) (LamS-elim N)
  LamS-elim (lam M) = lam* (LamS-elim M)

LamP : ∀ {n} → LamS n → ℕ → Type 
LamP {n} var m = n ≡ m
LamP (app M N) m = LamP M m ⊎ LamP N m
LamP {n} (lam M) m = LamP {suc n} M m

Lam : IndexedContainer
Lam .S = LamS
Lam .P = LamP

-- Claim: Well scoped lambda terms are ⟦ Lam ⟧ Fin 0
open import Cubical.Data.Fin using (Fin)

[_,_] = Sum.rec 
subst′ : {A : Type} (B : A → Type) {x y : A} → B x → x ≡ y → B y
subst′ B bx p = subst B p bx

sf : {x y : ℕ} → Fin x → x ≡ y → Fin y
sf = subst′ Fin

open import IndexedMonad ℕ Lam

private
  lam-ricms-• : ∀ {i} (s : LamS i) → ({j : ℕ} → LamP s j → LamS j) → LamS i
  lam-ricms-• var       σ = σ refl
  lam-ricms-• (app M N) σ = app (lam-ricms-• M (inl » σ)) (lam-ricms-• N (inr » σ))
  lam-ricms-• (lam M)   σ = lam (lam-ricms-• M σ)
  
  lam-ricms-↑ : ∀ {i} 
    (s : LamS i) 
    (s′ : {j : ℕ} → LamP s j → LamS j) 
    {j : ℕ} 
    (p : LamP (lam-ricms-• s s′) j) 
    → ℕ
  lam-ricms-↑ {i} var _ _ = i
  lam-ricms-↑ (app M N) σ (inl p) = lam-ricms-↑ M (inl » σ) p
  lam-ricms-↑ (app M N) σ (inr p) = lam-ricms-↑ N (inr » σ) p 
  lam-ricms-↑ (lam M) σ p = lam-ricms-↑ M σ p

  lam-ricms-↖ : ∀ {i} 
    (s : LamS i) 
    (s′ : {j : ℕ} → LamP s j → LamS j) 
    {j : ℕ} 
    (p : LamP (lam-ricms-• s s′) j) 
    → LamP s (lam-ricms-↑ s s′ p)
  lam-ricms-↖ var σ p = refl
  lam-ricms-↖ (app M N) σ (inl p) = inl (lam-ricms-↖ M (inl » σ) p)
  lam-ricms-↖ (app M N) σ (inr p) = inr (lam-ricms-↖ N (inr » σ) p)
  lam-ricms-↖ (lam M) σ p = lam-ricms-↖ M σ p

  lam-ricms-↗ : ∀ {i}
    (s : LamS i) 
    (s′ : {j : ℕ} → LamP s j → LamS j) 
    {j : ℕ} 
    (p : LamP (lam-ricms-• s s′) j) 
    → LamP (s′ (lam-ricms-↖ s s′ p)) j
  lam-ricms-↗ var σ p = p
  lam-ricms-↗ (app M N) σ (inl p) = lam-ricms-↗ M (inl » σ) p
  lam-ricms-↗ (app M N) σ (inr p) = lam-ricms-↗ N (inr » σ) p
  lam-ricms-↗ (lam M) σ p = lam-ricms-↗ M σ p

module _ where
  open RawICMS
  lam-ricms : RawICMS
  lam-ricms .e n = var
  lam-ricms ._•_ {i} = lam-ricms-• {i}
  lam-ricms ._↑_ {s} = lam-ricms-↑ s 
  lam-ricms ._↖_ {s} = lam-ricms-↖ s
  lam-ricms ._↗_ {s} = lam-ricms-↗ s
  lam-ricms .P-e-idx = idfun _

open isICMS
open import Cubical.Data.Nat using (isSetℕ)
open import Cubical.Functions.FunExtEquiv using (funExtDep)

private
  open RawICMS lam-ricms
  lam-isicms-e-unit-l : ∀ {i} (s : LamS i) → lam-ricms-• s (λ _ → var) ≡ s
  lam-isicms-e-unit-l var = refl
  lam-isicms-e-unit-l (app M N) = cong₂ app (lam-isicms-e-unit-l M) (lam-isicms-e-unit-l N)
  lam-isicms-e-unit-l (lam M) = cong lam (lam-isicms-e-unit-l M)

  lam-isicms-↖-unit-l : ∀ {i} (s : LamS i) {j : ℕ} →
      PathP (λ z → LamP (lam-isicms-e-unit-l s z) j → LamP s j)
      (λ p → transp (λ i₁ → LamP s (lam-ricms-↗ s (λ {j = j₁} _ → var) p i₁)) i0 (lam-ricms-↖ s (λ _ → var) p))
      (λ p → p)
  lam-isicms-↖-unit-l {i} var {j} ι p = transp (λ κ → i ≡ p (ι ∨ κ)) ι (λ κ → p (ι ∧ κ))
  lam-isicms-↖-unit-l (app M N) {j} ι (inl p) = inl (funExtConstCod (congP (λ ι → lam-isicms-↖-unit-l M {j} ι)) ι p)
  lam-isicms-↖-unit-l (app M N) {j} ι (inr p) = inr (funExtConstCod (congP (λ ι → lam-isicms-↖-unit-l N {j} ι)) ι p) 
  lam-isicms-↖-unit-l (lam M) = lam-isicms-↖-unit-l M 

  lam-isicms-•-assoc : ∀ {i}
      (s : LamS i) (s′ : {j : ℕ} → LamP s j → LamS j)
      (s″ : {j k : ℕ} (p : LamP s k) → LamP (s′ p) j → LamS j) →
      lam-ricms-• (lam-ricms-• s s′) (smoosh {s = s} s″) ≡
      lam-ricms-• s (_Π•_ {s = s} s′ s″)
  lam-isicms-•-assoc var s′ s″ = refl
  lam-isicms-•-assoc (app M N) s′ s″ = cong₂ app
    (lam-isicms-•-assoc M (inl » s′) (inl » s″))
    (lam-isicms-•-assoc N (inr » s′) (inr » s″))
  lam-isicms-•-assoc (lam M) s′ s″ = cong lam (lam-isicms-•-assoc M s′ s″)

  lam-isicms-↖↑-↑-assoc : ∀ {i} {j}
    (s : LamS i) (s′ : {j : ℕ} → LamP s j → LamS j)
    (s″ : {j : ℕ} {k : ℕ} (p : LamP s k) → LamP (s′ p) j → LamS j)
    → PathP (λ ι → LamP (lam-isicms-•-assoc s s′ s″ ι) j → ℕ)
    (lam-ricms-↖ (lam-ricms-• s s′) (smoosh {s = s} s″) » lam-ricms-↑ s s′)
    (lam-ricms-↑ s (_Π•_ {s = s} s′  s″))
  lam-isicms-↖↑-↑-assoc var s′ s″ = refl
  lam-isicms-↖↑-↑-assoc (app M N) s′ s″ ι (inl p) = lam-isicms-↖↑-↑-assoc M (inl » s′) (inl » s″) ι p
  lam-isicms-↖↑-↑-assoc (app M N) s′ s″ ι (inr p) = lam-isicms-↖↑-↑-assoc N (inr » s′) (inr » s″) ι p
  lam-isicms-↖↑-↑-assoc (lam M) s′ s″ = lam-isicms-↖↑-↑-assoc M s′ s″

  lam-isicms-↑-↗↑-assoc : ∀ {i} {j}
    (s : LamS i) (s′ : {j : ℕ} → LamP s j → LamS j)
    (s″ : {j : ℕ} {k : ℕ} (p : LamP s k) → LamP (s′ p) j → LamS j)
    → PathP (λ ι → LamP (lam-isicms-•-assoc s s′ s″ ι) j → ℕ)
      (lam-ricms-↑ (lam-ricms-• s s′) (smoosh {s = s} s″))
      (λ p → lam-ricms-↑ (s′ (lam-ricms-↖ s (_Π•_ {s = s} s′  s″) p)) (s″ (lam-ricms-↖ s (_Π•_ {s = s} s′  s″) p)) (lam-ricms-↗ s (_Π•_ {s = s} s′  s″) p))
  lam-isicms-↑-↗↑-assoc var s′ s″ = refl
  lam-isicms-↑-↗↑-assoc (app M N) s′ s″ ι (inl p) = lam-isicms-↑-↗↑-assoc M (inl » s′) (inl » s″) ι p
  lam-isicms-↑-↗↑-assoc (app M N) s′ s″ ι (inr p) = lam-isicms-↑-↗↑-assoc N (inr » s′) (inr » s″) ι p
  lam-isicms-↑-↗↑-assoc (lam M) s′ s″ = lam-isicms-↑-↗↑-assoc M s′ s″

  lam-isicms-↖↖-↖-assoc : ∀ {i} {j}
    (s : LamS i) (s′ : {j : ℕ} → LamP s j → LamS j)
    (s″ : {j : ℕ} {k : ℕ} (p : LamP s k) → LamP (s′ p) j → LamS j)
    → PathP
      (λ ι →
         (p : LamP (lam-isicms-•-assoc s s′ s″ ι) j) →
         LamP s (lam-isicms-↖↑-↑-assoc s s′ s″ ι p))
      (lam-ricms-↖ (lam-ricms-• s s′) (smoosh {s = s} s″) » lam-ricms-↖ s s′) 
      (lam-ricms-↖ s (_Π•_ {s = s} s′ s″))
  lam-isicms-↖↖-↖-assoc var s′ s″ = refl
  lam-isicms-↖↖-↖-assoc (app M N) s′ s″ ι (inl p) = inl (lam-isicms-↖↖-↖-assoc M (inl » s′) (inl » s″) ι p)
  lam-isicms-↖↖-↖-assoc (app M N) s′ s″ ι (inr p) = inr (lam-isicms-↖↖-↖-assoc N (inr » s′) (inr » s″) ι p)
  lam-isicms-↖↖-↖-assoc (lam M) = lam-isicms-↖↖-↖-assoc M

  lam-isicms-↖↗-↗↖-assoc : ∀ {i} {j}
    (s : LamS i) (s′ : {j : ℕ} → LamP s j → LamS j)
    (s″ : {j : ℕ} {k : ℕ} (p : LamP s k) → LamP (s′ p) j → LamS j) 
    → PathP
      (λ ι →
         (p : LamP (lam-isicms-•-assoc s s′ s″ ι) j) →
         LamP (s′ (lam-isicms-↖↖-↖-assoc s s′ s″ ι p))
         (lam-isicms-↑-↗↑-assoc s s′ s″ ι p))
      (λ p → lam-ricms-↗ s s′ (lam-ricms-↖ (lam-ricms-• s s′) (smoosh {s = s} s″) p))
      (λ p →
         lam-ricms-↖ (s′ (lam-ricms-↖ s (_Π•_ {s = s} s′ s″) p))
         (s″ (lam-ricms-↖ s (_Π•_ {s = s} s′ s″) p)) (lam-ricms-↗ s (_Π•_ {s = s} s′ s″) p))
  lam-isicms-↖↗-↗↖-assoc var s′ s″ = refl
  lam-isicms-↖↗-↗↖-assoc (app M N) s′ s″ ι (inl p) = lam-isicms-↖↗-↗↖-assoc M (inl » s′) (inl » s″) ι p
  lam-isicms-↖↗-↗↖-assoc (app M N) s′ s″ ι (inr p) = lam-isicms-↖↗-↗↖-assoc N (inr » s′) (inr » s″) ι p 
  lam-isicms-↖↗-↗↖-assoc (lam M) = lam-isicms-↖↗-↗↖-assoc M

  lam-isicms-↗-↗↗-assoc : ∀ {i} {j}
    (s : LamS i) (s′ : {j : ℕ} → LamP s j → LamS j)
    (s″ : {j : ℕ} {k : ℕ} (p : LamP s k) → LamP (s′ p) j → LamS j) 
    → PathP
      (λ ι →
         (p : LamP (lam-isicms-•-assoc s s′ s″ ι) j)
         → LamP (s″ (lam-isicms-↖↖-↖-assoc s s′ s″ ι p) (lam-isicms-↖↗-↗↖-assoc s s′ s″ ι p)) j)
      (lam-ricms-↗ (lam-ricms-• s s′) (smoosh {s = s} s″))
      (λ p →
         lam-ricms-↗ (s′ (lam-ricms-↖ s (_Π•_ {s = s} s′ s″) p))
         (s″ (lam-ricms-↖ s (_Π•_ {s = s} s′ s″) p)) (lam-ricms-↗ s (_Π•_ {s = s} s′ s″) p))
  lam-isicms-↗-↗↗-assoc var s′ s″ = refl
  lam-isicms-↗-↗↗-assoc (app M N) s′ s″ ι (inl p) = lam-isicms-↗-↗↗-assoc M (inl » s′) (inl » s″) ι p
  lam-isicms-↗-↗↗-assoc (app M N) s′ s″ ι (inr p) = lam-isicms-↗-↗↗-assoc N (inr » s′) (inr » s″) ι p
  lam-isicms-↗-↗↗-assoc (lam M) = lam-isicms-↗-↗↗-assoc M

lam-isicms : isICMS lam-ricms
lam-isicms .e-unit-l = lam-isicms-e-unit-l
lam-isicms .↖-unit-l = lam-isicms-↖-unit-l
lam-isicms .e-unit-r s = substRefl {B = LamS} s
lam-isicms .↗-unit-r {i} s {j} ι p = transp (λ κ → LamP {n = i} (substRefl {B = LamS} s (ι ∨ κ)) j) ι p
lam-isicms .•-assoc = lam-isicms-•-assoc
lam-isicms .↑-↗↑-assoc = lam-isicms-↑-↗↑-assoc 
lam-isicms .↖↑-↑-assoc = lam-isicms-↖↑-↑-assoc
lam-isicms .↖↖-↖-assoc = lam-isicms-↖↖-↖-assoc
lam-isicms .↖↗-↗↖-assoc = lam-isicms-↖↗-↗↖-assoc
lam-isicms .↗-↗↗-assoc = lam-isicms-↗-↗↗-assoc 

-- module IwilareDeBruijn where
--
--   infix  9  #_
--   infixl 7  _·_
--   infix  6  ƛ_
--
--   data Term : ℕ → Set where
--     #_  : ∀ {n : ℕ} → Fin n           → Term n
--     ƛ_  : ∀ {n : ℕ} → Term (suc n)    → Term n
--     _·_ : ∀ {n : ℕ} → Term n → Term n → Term n
--
  -- open import Cubical.Foundations.Isomorphism
  -- open Iso
  -- open import Cubical.Data.Sigma using (ΣPathP)
  --
  -- {-# TERMINATING #-}
  -- Term-LamFin-iso : ∀ n → Iso (Term n) (⟦ Lam ⟧ Fin n)
  -- Term-LamFin-iso n .fun = f n
  --   where
  --   f : ∀ n → Term n → ⟦ Lam ⟧ Fin n 
  --   f n (# x) = var , sf x
  --   f n (ƛ t) = let (s , px) = f (suc n) t in lam s , px
  --   f n (t · q) = 
  --     let
  --       s  , px  = f n t
  --       s′ , px′ = f n q
  --     in app s s′ , [ px , px′ ]
  -- Term-LamFin-iso n .inv = g n
  --   where
  --   g : ∀ n → ⟦ Lam ⟧ Fin n → Term n
  --   g n (var , px) = # px refl
  --   g n (app M N , px) = g n (M , inl » px) · g n (N , inr » px)
  --   g n (lam M , px) = ƛ g (suc n) (M , px)
  -- Term-LamFin-iso n .rightInv (var , px) = ΣPathP (refl , implicitFunExt λ {_} → funExt λ p → λ ι → transp (λ κ → Fin (p (ι ∨ κ))) ι (px (λ κ → p (ι ∧ κ))))
  -- Term-LamFin-iso n .rightInv (app s s₁ , px) = {! !}
  -- Term-LamFin-iso n .rightInv (lam s , px) = {! !}
  -- Term-LamFin-iso n .leftInv (# x) = cong #_ (substRefl {B = Fin} x)
  -- Term-LamFin-iso n .leftInv (ƛ t) = {! !}
  -- Term-LamFin-iso n .leftInv (t · t₁) = {! !}

module MakeSense where
  Term = ⟦ Lam ⟧ Fin

  λ1⟨00⟩ : Term 1
  λ1⟨00⟩ .fst = lam (app var (app var var))
  λ1⟨00⟩ .snd = [ sf 1 , [ sf 0 , sf 0 ] ]

  Y-comb : Term 0
  Y-comb .fst = lam (app (λ1⟨00⟩ .fst) (λ1⟨00⟩ .fst))
  Y-comb .snd = [ λ1⟨00⟩ .snd , λ1⟨00⟩ .snd ]

  Y-comb² : ⟦ Lam ⟧ (Term) 0
  Y-comb² .fst = lam (app var var)
  Y-comb² .snd = [ subst′ Term λ1⟨00⟩ , subst′ Term λ1⟨00⟩ ]

