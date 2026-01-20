{-# OPTIONS --cubical --guardedness #-}
{-
This file defines Leibniz products and exponentials on Map. It also
proves their adjointness.
-}
module LeibnizConstruction.Map where
-- Local imports
open import Prelude
open import PushoutProdFib
open import Categories.ProtoWildCat
open import Categories.Map
open import Categories.Fam
open import Categories.FamMapEquiv
open import LeibnizConstruction.Fam
open import LeibnizConstruction.Adjunction
open import LeibnizConstruction.Fam

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv

open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.PushoutProduct

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open hasBiProtoFunctorStructure
open Iso

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Type ℓ₁
    B : Type ℓ₂
    X : Type ℓ₃
    Y : Type ℓ₄

------------ Leibniz construction (on Map) -------------------
------- Leibniz exponential -----------
-- Target of the Leibniz exponential
T[_⋔_] : (f : A → B) (g : X → Y) → Type _
T[_⋔_] {A = A} {B = B} {X = X} {Y = Y} f g =
  Σ[ l ∈ (B → Y) ] Σ[ r ∈ (A → X) ] (l ∘ f ≡ g ∘ r)

-- The map
_⋔_ : (f : A → B) (g : X → Y) → (B → X) → T[ f ⋔ g ]
(f ⋔ g) h .fst = g ∘ h
(f ⋔ g) h .snd .fst = h ∘ f
(f ⋔ g) h .snd .snd = refl

-- On the category of maps
_⋔ᵐ_ : Map ℓ₁ → Map ℓ₂ → Map _
((A , B , f) ⋔ᵐ (X , Y , g)) .fst = B → X
((A , B , f) ⋔ᵐ (X , Y , g)) .snd .fst = T[ f ⋔ g ]
((A , B , f) ⋔ᵐ (X , Y , g)) .snd .snd = f ⋔ g

------- Leibniz product -----------
-- Source of the Leibniz product (imported and renamed)
S[_⊠_] : (f : A → B) (g : X → Y) → Type _
S[_⊠_] {A = A} {B = B} {X = X} {Y = Y} = PushProd

-- The map (imported and renamed)
_⊠_ : (f : A → B) (g : X → Y) → S[ f ⊠ g ] → B × Y
_⊠_ = _×̂_

-- On the category of maps
_⊠ᵐ_ : Map ℓ₁ → Map ℓ₂ → Map _
((A , B , f) ⊠ᵐ (X , Y , g)) .fst = S[ f ⊠ g ]
((A , B , f) ⊠ᵐ (X , Y , g)) .snd .fst = B × Y
((A , B , f) ⊠ᵐ (X , Y , g)) .snd .snd = f ⊠ g

-- Goal now: show functoriality and adjointness. Since we know that
-- these properties are satisfied by the analoguous constructions on
-- Fam, we can transport these results over back to Map. To this end,
-- we need to show that the Leibniz construction is preserved by the
-- equivalence Fam ≃ Map.

-- ⋔ is preserved
Fam→MapPres⋔ : {C : Fam ℓ₁} {D : Fam ℓ₂}
     → (Fam→Map C ⋔ᵐ Fam→Map D) ≃Map (Fam→Map (C ⋔ᶠ D))
Fam→MapPres⋔ .fst = isoToEquiv (invIso Iso-TotFam⋔ᶠ-[BaseFam→TotFam])
Fam→MapPres⋔ {C = A , B} {D = X , Y} .snd .fst =
  isoToEquiv (Σ-cong-iso-snd λ F
    → compIso (compIso (Σ-cong-iso-snd λ Q → invIso funExtIso)
      (compIso (invIso (Σ-Π-Iso {B = λ _ → Σ X Y} {C = λ f a → F (fst f) ≡ fst a}))
      (codomainIsoDep λ a → compIso Σ-assoc-Iso
        (compIso (Σ-cong-iso-snd (λ x → Σ-swap-Iso))
         (compIso (invIso Σ-assoc-Iso)
          (compIso (Σ-cong-iso (isContr→Iso (isContrSingl _) isContrUnit)
            λ t → equivToIso (substEquiv Y (sym (snd t)))) lUnit×Iso))))))
      curryIso)
Fam→MapPres⋔ .snd .snd F =
 ΣPathP (refl , (funExt (λ t → funExt λ b → transportRefl (F t .snd))))

Fam→MapPres⋔≡ : {C : Fam ℓ₁} {D : Fam ℓ₂}
     → (Fam→Map C ⋔ᵐ Fam→Map D) ≡ (Fam→Map (C ⋔ᶠ D))
Fam→MapPres⋔≡ = invEq univalenceMap Fam→MapPres⋔

-- ⋔ is preserved (alt. statement)
Fam→MapPres⋔≡' : {C : Map ℓ₁} {D : Map ℓ₂}
     → Fam→Map (Map→Fam C ⋔ᶠ Map→Fam D) ≡ (C ⋔ᵐ D)
Fam→MapPres⋔≡' {C = C} {D} =
  sym (invEq univalenceMap Fam→MapPres⋔)
  ∙ cong₂ _⋔ᵐ_ (sec Iso-Fam-Map C) (sec Iso-Fam-Map D)

-- ⊠ is preserved
Map→FamPres⊠ : {C : Map ℓ₁} {D : Map ℓ₂}
  → Map→Fam (C ⊠ᵐ D) ≃Fam (Map→Fam C ⊠ᶠ Map→Fam D)
Map→FamPres⊠ .fst = idEquiv _
Map→FamPres⊠ .snd (c , d) = Fib×^≃JoinFib c d

Map→FamPres⊠≡ : {C : Map ℓ₁} {D : Map ℓ₂}
  → Map→Fam (C ⊠ᵐ D) ≡ (Map→Fam C ⊠ᶠ Map→Fam D)
Map→FamPres⊠≡ = invEq univalenceFam Map→FamPres⊠

-- ⊠ is preserved (alt. statement)
Fam→MapPres⊠≡ : {C : Map ℓ₁} {D : Map ℓ₂}
     → Fam→Map (Map→Fam C ⊠ᶠ Map→Fam D) ≡ (C ⊠ᵐ D)
Fam→MapPres⊠≡ {C = C} {D} =
  cong Fam→Map (sym Map→FamPres⊠≡)
  ∙ sec Iso-Fam-Map _

-- Technical result used for transporting from Fam to Map
transportLeibnizConstruction :
  (P : (C : ProtoWildCat (ℓ-suc ℓ₁) ℓ₁)
       (f g : fst C → fst C → fst C) → Type ℓ₃)
  → P ⌈ 𝑭𝑨𝑴 ℓ₁ ⌉ _⊠ᶠ_ _⋔ᶠ_
   ≡ P ⌈ 𝑴𝑨𝑷 ℓ₁ ⌉ _⊠ᵐ_ _⋔ᵐ_
transportLeibnizConstruction P =
  transportAlongWildEquiv _ _ 𝑭𝑨𝑴≅ᴾᵂ𝑴𝑨𝑷 P _⊠ᶠ_ _⊠ᵐ_
    (funExt (λ C → funExt λ D → Fam→MapPres⊠≡))
    _⋔ᶠ_ _⋔ᵐ_
    (funExt (λ C → funExt (λ D → Fam→MapPres⋔≡')))
  where
  transportAlongWildEquiv :
    (C C' : ProtoWildCat ℓ₁ ℓ₂) (E : C ≅ᴾᵂ C')
    (P : (C : ProtoWildCat ℓ₁ ℓ₂) (f g : fst C → fst C → fst C) → Type ℓ₃)
    (L : fst C → fst C → fst C) (L'  : fst C' → fst C' → fst C')
    (L≡L' : (λ x y → fst (fst E) (L (invEq (_ , fst (snd E)) x)
                                     (invEq (_ , fst (snd E)) y))) ≡ L')
    (R : fst C → fst C → fst C) (R'  : fst C' → fst C' → fst C')
    (R≡R' : (λ x y → fst (fst E) (R (invEq (_ , fst (snd E)) x)
                                     (invEq (_ , fst (snd E)) y))) ≡ R')
    → P C L R ≡ P C' L' R'
  transportAlongWildEquiv C =
    JProtoWildCat _ λ _ _ → J> λ _ → J> refl

-- The main lemma
abstract
  areAdjointBiFunctors-×ᵐ-⋔ᵐ :
    areAdjointBiFunctors ⌈ 𝑴𝑨𝑷 ℓ₁ ⌉ _⊠ᵐ_ _⋔ᵐ_
  areAdjointBiFunctors-×ᵐ-⋔ᵐ =
    transport (transportLeibnizConstruction areAdjointBiFunctors)
      areAdjointBiFunctors-⊠ᶠ-⋔ᶠ

-- Let us spell out these properties, like we did for the Leibniz
-- construction on Fam.
hasBiProtoFunctorStructure⋔ᵐ :
  hasBiProtoFunctorStructure (⌈ 𝑴𝑨𝑷 ℓ₁ ⌉ ^opᵖʳ) ⌈ 𝑴𝑨𝑷 ℓ₁ ⌉ ⌈ 𝑴𝑨𝑷 ℓ₁ ⌉ _⋔ᵐ_
hasBiProtoFunctorStructure⋔ᵐ = areAdjointBiFunctors-×ᵐ-⋔ᵐ .snd .fst

hasBiProtoFunctorStructure⊠ᵐ :
  hasBiProtoFunctorStructure ⌈ 𝑴𝑨𝑷 ℓ₁ ⌉ ⌈ 𝑴𝑨𝑷 ℓ₁ ⌉ ⌈ 𝑴𝑨𝑷 ℓ₁ ⌉ _⊠ᵐ_
hasBiProtoFunctorStructure⊠ᵐ = areAdjointBiFunctors-×ᵐ-⋔ᵐ .fst

-- Functorial action, explicitly
⋔ᵐ→ₗ : (A B C : Map ℓ₁) → Map[ A , B ] → Map[ B ⋔ᵐ C , A ⋔ᵐ C ]
⋔ᵐ→ₗ A B C f = leftAct (hasBiProtoFunctorStructure⋔ᵐ) C .fst f

⋔ᵐ→ᵣ : (A B C : Map ℓ₁) → Map[ B , C ] →  Map[ A ⋔ᵐ B , A ⋔ᵐ C ]
⋔ᵐ→ᵣ A B C f = rightAct (hasBiProtoFunctorStructure⋔ᵐ) A .fst {x = B} {C} f

⊠ᵐ→ₗ : (A B C : Map ℓ₁) → Map[ A , B ] → Map[ A ⊠ᵐ C , B ⊠ᵐ C ]
⊠ᵐ→ₗ A B C f = leftAct (hasBiProtoFunctorStructure⊠ᵐ) C .fst f

⊠ᵐ→ᵣ : (A B C : Map ℓ₁) → Map[ B , C ] → Map[ A ⊠ᵐ B , A ⊠ᵐ C ]
⊠ᵐ→ᵣ A B C f = rightAct (hasBiProtoFunctorStructure⊠ᵐ) A .fst {x = B} {C} f

-- Adjointness statement
wildBiAdjoint-⊠ᵐ-⋔ᵐ : wildBiAdjoint ⌈ 𝑴𝑨𝑷 ℓ₁ ⌉ _⊠ᵐ_ _⋔ᵐ_
                      hasBiProtoFunctorStructure⊠ᵐ
                      hasBiProtoFunctorStructure⋔ᵐ
wildBiAdjoint-⊠ᵐ-⋔ᵐ = areAdjointBiFunctors-×ᵐ-⋔ᵐ .snd .snd

-- Associativity
assoc⊠ᵐ : ∀ {ℓ₃} (f : Map ℓ₁) (g : Map ℓ₂) (h : Map ℓ₃)
  → ((f ⊠ᵐ g) ⊠ᵐ h) ≡ (f ⊠ᵐ(g ⊠ᵐ h))
assoc⊠ᵐ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₃} f g h =
    sym (Fam→MapPres⊠≡ {C = (f ⊠ᵐ g)} {D = h})
  ∙ cong Fam→Map lem
  ∙ Fam→MapPres⊠≡ {C = f} {D = (g ⊠ᵐ h)}
  where
  f* = Map→Fam f
  g* = Map→Fam g
  h* = Map→Fam h

  lem : Map→Fam (f ⊠ᵐ g) ⊠ᶠ h*
      ≡ f* ⊠ᶠ Map→Fam (g ⊠ᵐ h)
  lem = cong (_⊠ᶠ h*)
         (cong Map→Fam (sym Fam→MapPres⊠≡)
       ∙  invEq (univalenceFam
             {A = Map→Fam (Fam→Map (f* ⊠ᶠ g*))}
             {B = f* ⊠ᶠ g*})
            (Fam→Map→Fam (f* ⊠ᶠ g*)))
      ∙ sym (cong (f* ⊠ᶠ_)
             (sym (cong Map→Fam (Fam→MapPres⊠≡ {C = g} {h})))
           ∙ cong₂ _⊠ᶠ_ refl
             (invEq (univalenceFam
                    {A = Map→Fam (Fam→Map (g* ⊠ᶠ h*))}
                    {B = g* ⊠ᶠ h*})
                    (Fam→Map→Fam (g* ⊠ᶠ h*)))
           ∙ sym (invEq (univalenceFam
                        {A = (f* ⊠ᶠ g*) ⊠ᶠ h*}
                        {B = f* ⊠ᶠ (g* ⊠ᶠ h*)})
                 (assoc⊠ᶠ f* g* h*)))

-- Commuatativity
comm⊠ᵐS→ : {f : A → B} {g : X → Y}
  → S[ f ⊠ g ] → S[ g ⊠ f ]
comm⊠ᵐS→ =
  rec∣inl (a , y) ↦ inr (y , a)
     ∣inr (b , x) ↦ inl (x , b)
     ∣push (a , x) ↦ sym (push (x , a))

comm⊠ᵐS→² : {f : A → B} {g : X → Y} (x : S[ f ⊠ g ])
  → comm⊠ᵐS→ (comm⊠ᵐS→ x) ≡ x
comm⊠ᵐS→² =
  elim∣inl (a , y) ↦ refl
      ∣inr (b , x) ↦ refl
      ∣push (a , x) ↦ λ i _ → push (a , x) i

comm⊠ᵐSIso : {f : A → B} {g : X → Y} → Iso S[ f ⊠ g ] S[ g ⊠ f ]
comm⊠ᵐSIso .fun = comm⊠ᵐS→
comm⊠ᵐSIso .inv = comm⊠ᵐS→
comm⊠ᵐSIso .sec = comm⊠ᵐS→²
comm⊠ᵐSIso .ret = comm⊠ᵐS→²

comm⊠ᵐ : (f : Map ℓ₁) (g : Map ℓ₂) → (f ⊠ᵐ g) ≃Map (g ⊠ᵐ f)
comm⊠ᵐ _ _ .fst = isoToEquiv comm⊠ᵐSIso
comm⊠ᵐ _ _ .snd .fst = isoToEquiv Σ-swap-Iso
comm⊠ᵐ (A , B , f) (X , Y , g) .snd .snd =
  elim∣inl (a , y) ↦ refl
     ∣inr (b , x) ↦ refl
     ∣push (a , x) ↦ λ i _ → g x , f a

-- Formula describing the interaction between ⊠ᵐ and ⋔ᵐ
Iso-[[⊠ᵐ]-⋔ᵐ]-[⋔ᵐ-[⋔ᵐ]] : (A B C : Map ℓ₁) → (A ⊠ᵐ B) ⋔ᵐ C ≡ A ⋔ᵐ (B ⋔ᵐ C)
Iso-[[⊠ᵐ]-⋔ᵐ]-[⋔ᵐ-[⋔ᵐ]] =
  transport lem λ A B C → invEq univalenceFam (Iso-[[⊠ᶠ]-⋔ᶠ]-[⋔ᶠ-[⋔ᶠ]] A B C)
  where
  lem = transportLeibnizConstruction λ Fam _⊠ᶠ_ _⋔ᶠ_ →
         ((A B C : fst Fam) → ((A ⊠ᶠ B) ⋔ᶠ C) ≡ (A ⋔ᶠ (B ⋔ᶠ C)))
