open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor 
open import Cubical.Data.Sigma using (_×_)

open import Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.TwoDiscrete
open import GpdCont.TwoCategory.StrictFunctor
open import GpdCont.WildCat.NatTrans 


module IndexedGpdContainer
  (I : Type)
  (isGpdI : isGroupoid I)
  where

open import Definitions I
open import IndexedContainer I

open TwoCategory
open TwoCategoryStr
open IsTwoCategory
open WildCat

WildGpdI : WildCat _ _
WildGpdI .ob = Σ[ X ∈ IType ] ∀ i → isGroupoid (X i) 
WildGpdI .Hom[_,_] (X , _) (Y , _) = X i→ Y
WildGpdI .id f = idfun _
WildGpdI ._⋆_ = _i»_
WildGpdI .⋆IdL f = refl
WildGpdI .⋆IdR f = refl
WildGpdI .⋆Assoc f g h = refl

GpdI : TwoCategory _ _ _
GpdI = TwoDiscrete WildGpdI λ X Y → isGroupoidΠ2 λ i _ → Y .snd i

open WildNatTrans

-- Boilerplate stolen and adapted from https://github.com/phijor/cubical-containers/
idNat : (F : WildFunctor WildGpdI WildGpdI) → WildNatTrans _ _ F F
idNat F .N-ob x i = idfun _
idNat F .N-hom f = refl

module composite {F G H : WildFunctor WildGpdI WildGpdI} (α : WildNatTrans _ _ F G) (β : WildNatTrans _ _ G H) where
  module G = WildFunctor G
  module F = WildFunctor F
  module H = WildFunctor H
  module α = WildNatTrans α
  module β = WildNatTrans β

  composite-ob : (x : WildGpdI .ob) → WildGpdI [ F.F-ob x , H.F-ob x ]
  composite-ob x = (α.N-ob x) i» (β.N-ob x) 

  composite-hom : ∀ (x y : WildGpdI .ob) (f : WildGpdI [ x , y ])
    → (F.F-hom f) i» (composite-ob y) ≡ (composite-ob x) i» H.F-hom f
  composite-hom x y f = congS (_i» (β.N-ob y)) (α.N-hom f) ∙ congS ( α.N-ob x i»_) (β.N-hom f)

  composite : WildNatTrans _ _ F H
  composite .WildNatTrans.N-ob = composite-ob
  composite .WildNatTrans.N-hom {x} {y} = composite-hom x y

open composite using () renaming (composite to _⊛_ ; composite-hom to ⊛-hom) public

idNatTransₗ : ∀ {F G : WildFunctor WildGpdI WildGpdI} (α : WildNatTrans _ _ F G) → (idNat F) ⊛ α ≡ α
idNatTransₗ {F} {G} α = WildNatTransPath
  (λ x → refl)
  (λ {x} {y} f → sym (GL.lUnit (α .WildNatTrans.N-hom f)))

idNatTransᵣ : ∀ {F G : WildFunctor WildGpdI WildGpdI} (α : WildNatTrans _ _ F G) → α ⊛ (idNat G) ≡ α
idNatTransᵣ {F} {G} α = WildNatTransPath
  (λ x → refl)
  (λ {x} {y} f → sym (GL.rUnit (α .WildNatTrans.N-hom f)))

assocNatTrans : ∀ {F G H K : WildFunctor WildGpdI WildGpdI} (α : WildNatTrans _ _ F G) (β : WildNatTrans _ _ G H) (γ : WildNatTrans _ _ H K) →
  (α ⊛ β) ⊛ γ
    ≡
  α ⊛ (β ⊛ γ)
assocNatTrans {F} {G} {H} {K} α β γ = WildNatTransPath (λ x → refl) assoc where
  module F = WildFunctor F
  module G = WildFunctor G
  module H = WildFunctor H
  module K = WildFunctor K

  open WildNatTrans

  assoc : ∀ {x y} f → composite.composite-hom (α ⊛ β) γ x y f ≡ composite.composite-hom α (β ⊛ γ) x y f
  assoc {x} {y} f =
    congS (_i» (γ .N-ob y)) ((α ⊛ β) .N-hom f) ∙ congS ((α ⊛ β) .N-ob x i»_) (γ .N-hom f)
      ≡⟨ cong (_∙ cong ((α ⊛ β) .N-ob x i»_) (γ .N-hom f)) (GL.cong-∙ (_i» γ .N-ob y ) _ _) ⟩
    (_ ∙ _) ∙ cong ((α ⊛ β) .N-ob x i»_) (γ .N-hom f)
      ≡⟨ sym (GL.assoc _ _ _) ⟩
    congS (_i» ((β ⊛ γ) .N-ob y)) (α .N-hom f) ∙ _
      ≡⟨ cong (cong (_i» ((β ⊛ γ) .N-ob y) ) (α .N-hom f) ∙_) (sym (GL.cong-∙ ( α .N-ob x i»_) (congS (_i» (γ .N-ob _) ) (β .N-hom f)) (congS ( β .N-ob _ i»_) (γ .N-hom f))) )⟩
    congS (_i» ((β ⊛ γ) .N-ob y)) (α .N-hom f)
      ∙ congS (α .N-ob x i»_) (
        congS (_i» (γ .N-ob _)) (β .N-hom f)
        ∙ congS ( β .N-ob _ i»_) (γ .N-hom f)
      )
        ∎

WildGpdIEndo : WildCat _ _ 
WildGpdIEndo .ob = WildFunctor WildGpdI WildGpdI
WildGpdIEndo .Hom[_,_] = WildNatTrans WildGpdI WildGpdI
WildGpdIEndo .id = idNat _
WildGpdIEndo ._⋆_ = _⊛_
WildGpdIEndo .⋆IdL = idNatTransₗ
WildGpdIEndo .⋆IdR = idNatTransᵣ
WildGpdIEndo .⋆Assoc = assocNatTrans

isGroupoidEndoNatTrans : ∀ F G → isGroupoid (WildGpdIEndo [ F , G ])
isGroupoidEndoNatTrans F G = isGroupoidRetract {B = NatTrans′} toNatTrans′ fromNatTrans′ retr isGroupoidNatTrans′ where
  open WildFunctor
  NatTrans′ = Σ[ α ∈ (∀ X → F .F-ob X .fst i→ G .F-ob X .fst) ] (∀ X Y (f : X .fst i→ Y .fst) → F .F-hom f i» α Y ≡ α X i» G .F-hom f)

  isGroupoidNatTrans′ : isGroupoid NatTrans′
  isGroupoidNatTrans′ = isGroupoidΣ
    (isGroupoidΠ3 λ X i _ → G .F-ob X .snd i)
    (λ α → isGroupoidΠ3 λ X Y H → isOfHLevelPath 3 (isGroupoidΠ2 λ i _ → G .F-ob Y .snd i) _ _)

  toNatTrans′ : WildGpdIEndo [ F , G ] → NatTrans′
  toNatTrans′ α .fst = α .N-ob
  toNatTrans′ α .snd _ _ = α .N-hom

  fromNatTrans′ : NatTrans′ → WildGpdIEndo [ F , G ]
  fromNatTrans′ (α , α-hom) .N-ob = α
  fromNatTrans′ (α , α-hom) .N-hom = α-hom _ _

  retr : ∀ α → fromNatTrans′ (toNatTrans′ α) ≡ α
  retr α i .N-ob = α .N-ob
  retr α i .N-hom = α .N-hom

GpdIEndo : TwoCategory _ _ _
GpdIEndo = TwoDiscrete WildGpdIEndo isGroupoidEndoNatTrans

isGroupoidIC : IndexedContainer → Type
isGroupoidIC (S ⊲ P) =
  (∀ {i} → isGroupoid (S i))
  × (∀ {i} {s : S i} {j} → isGroupoid (P s j))

GpdIC = Σ[ ic ∈ IndexedContainer ] isGroupoidIC ic

WildGpdICont : WildCat _ _ 
WildGpdICont .ob = GpdIC
WildGpdICont .Hom[_,_] F G = F .fst ⇒ G .fst
WildGpdICont .id = id₁ _
WildGpdICont ._⋆_ = _;_
WildGpdICont .⋆IdL _ = refl
WildGpdICont .⋆IdR _ = refl
WildGpdICont .⋆Assoc _ _ _ = refl

GpdICont : TwoCategory _ _ _
GpdICont = TwoDiscrete WildGpdICont isGroupoid⇒
  where
  isGroupoid⇒ : (F G : GpdIC) → isGroupoid (F .fst ⇒ G .fst)
  isGroupoid⇒ (S ⊲ P , _ , isGpdP) (S′ ⊲ P′ , isGpdS′ , _) =
    isGroupoidΠ2 λ i s →
      isGroupoidΣ isGpdS′ λ s′ → isGroupoidImplicitΠ λ _ →
        isGroupoidΠ λ _ → isGpdP

module ⟦-⟧ where
  open StrictFunctor
  open import Cubical.Functions.FunExtEquiv

  Eval : GpdICont .ob → GpdIEndo .ob
  Eval (ic , isgpdic) .WildFunctor.F-ob (x , isgpdx) = ⟦ ic ⟧ x , λ i → isGroupoidΣ (isgpdic .fst) λ s → isGroupoidImplicitΠ λ j → isGroupoidΠ λ _ → isgpdx j
  Eval (ic , isgpdic) .WildFunctor.F-hom = _⟦$⟧_ _
  Eval (ic , isgpdic) .WildFunctor.F-id = funExt₂ λ i x → refl  
  Eval (ic , isgpdic) .WildFunctor.F-seq f g = funExt₂ λ i x → refl 

  EvalHom : ∀ {x} {y} → GpdICont .hom x y → GpdIEndo .hom (Eval x) (Eval y)
  EvalHom = {! !}

  ⟦-⟧ : StrictFunctor GpdICont GpdIEndo
  ⟦-⟧ .F-ob = Eval
  ⟦-⟧ .F-hom = EvalHom
  ⟦-⟧ .F-rel = {! !}
  ⟦-⟧ .F-rel-id = {! !}
  ⟦-⟧ .F-rel-trans = {! !}
  ⟦-⟧ .F-hom-comp = {! !}
  ⟦-⟧ .F-hom-id = {! !}
  ⟦-⟧ .F-assoc-filler-left = {! !}
  ⟦-⟧ .F-assoc-filler-right = {! !}
  ⟦-⟧ .F-assoc = {! !}
  ⟦-⟧ .F-unit-left-filler = {! !}
  ⟦-⟧ .F-unit-left = {! !}
  ⟦-⟧ .F-unit-right-filler = {! !}
  ⟦-⟧ .F-unit-right = {! !}
