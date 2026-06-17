{-# OPTIONS --cubical --guardedness #-}
{-
This file defines Leibniz products and exponentials on Fam
-}
module LeibnizConstruction.Fam where

-- Local imports
open import Prelude
open import Categories.WildPreorder
open import Categories.Fam

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.HITs.Pushout
open import Cubical.HITs.Join
  hiding (join) renaming (joinPushout to join)

private
  variable
    ℓ₁ ℓ₂ : Level

open Iso

------------ Leibniz construction (on Fam) -------------------
------- Leibniz exponential -----------
_⋔ᶠ_ : Fam ℓ₁ → Fam ℓ₂ → Fam _
((A , B) ⋔ᶠ (X , Y)) .fst = Fam[ (A , B) , (X , Y) ]
((A , B) ⋔ᶠ (X , Y)) .snd (m , μ) = (a : A) → Const (μ a)
------- Leibniz product -----------
_⊠ᶠ_ : Fam ℓ₁ → Fam ℓ₂ → Fam _
((A , B) ⊠ᶠ (X , Y)) .fst = A × X
((A , B) ⊠ᶠ (X , Y)) .snd (a , x) = join (B a) (Y x)

TotFam : Fam ℓ₁ → Type _
TotFam (A , B) = Σ A B

BaseFam : Fam ℓ₁ → Type _
BaseFam = fst

Iso-TotFam⋔ᶠ-[BaseFam→TotFam] : {AB : Fam ℓ₁} {XY : Fam ℓ₂}
   → Iso (TotFam (AB ⋔ᶠ XY)) (BaseFam AB → TotFam XY)
Iso-TotFam⋔ᶠ-[BaseFam→TotFam] {AB = (A , B)} {(X , Y)}=
  compIso Σ-assoc-Iso
    (compIso (Σ-cong-iso-snd (λ m
      → invIso (Σ-Π-Iso {B = λ a → B a → Y (m a)}
                         {C = λ _ f → Const f})))
          (compIso (invIso (Σ-Π-Iso {B = λ _ → X}
            {C = λ a x → Σ[ f ∈ (B a → Y x) ] Const f}))
            (codomainIsoDep λ a → Σ-cong-iso-snd λ x → TotConstIso)))

-- Functoriality
⋔ᶠ→ₗ : (A B C : Fam ℓ₁) → Fam[ A , B ] → Fam[ B ⋔ᶠ C , A ⋔ᶠ C ]
⋔ᶠ→ₗ A B C (F , P) .fst (T , Q) .fst = T ∘ F
⋔ᶠ→ₗ A B C (F , P) .fst (T , Q) .snd b x = Q (F b) (P b x)
⋔ᶠ→ₗ A B C (F , P) .snd (T , Q) x a .fst = x (F a) .fst
⋔ᶠ→ₗ A B C (F , P) .snd (T , Q) x a .snd a' = x (F a) .snd (P a a')

⋔ᶠ→ᵣ : (A B C : Fam ℓ₁) → Fam[ B , C ] →  Fam[ A ⋔ᶠ B , A ⋔ᶠ C ]
⋔ᶠ→ᵣ A B C (F , P) .fst (T , Q) .fst = F ∘ T
⋔ᶠ→ᵣ A B C (F , P) .fst (T , Q) .snd b x = P (T b) (Q b x)
⋔ᶠ→ᵣ A B C (F , P) .snd (T , Q) x a .fst = P (T a) (x a .fst)
⋔ᶠ→ᵣ A B C (F , P) .snd (T , Q) x a .snd a' = cong (P (T a)) (x a .snd a')

⊠ᶠ→ₗ : (A B C : Fam ℓ₁) → Fam[ A , B ] → Fam[ A ⊠ᶠ C , B ⊠ᶠ C ]
⊠ᶠ→ₗ A B C (F , P) .fst (b , c) .fst = F b
⊠ᶠ→ₗ A B C (F , P) .fst (b , c) .snd = c
⊠ᶠ→ₗ A B C (F , P) .snd (a , c) = joinPushout→ (P a) (idfun _)

⊠ᶠ→ᵣ : (A B C : Fam ℓ₁) → Fam[ B , C ] → Fam[ A ⊠ᶠ B , A ⊠ᶠ C ]
⊠ᶠ→ᵣ A B C (F , P) .fst (a , b) .fst = a
⊠ᶠ→ᵣ A B C (F , P) .fst (a , b) .snd = F b
⊠ᶠ→ᵣ A B C (F , P) .snd (a , b) = joinPushout→ (idfun _) (P b)

open hasBiWPFunctorStructure

-- Functoriality of _⋔ᶠ_
hasBiWPFunctorStructure⋔ᶠ :
  hasBiWPFunctorStructure (⌈ 𝑭𝑨𝑴 ℓ₁ ⌉ ^opʷᵖ) ⌈ 𝑭𝑨𝑴 ℓ₁ ⌉ ⌈ 𝑭𝑨𝑴 ℓ₁ ⌉ _⋔ᶠ_
hasBiWPFunctorStructure⋔ᶠ .leftAct d .fst = ⋔ᶠ→ₗ _ _ d
hasBiWPFunctorStructure⋔ᶠ .leftAct d .snd .fst x = refl
hasBiWPFunctorStructure⋔ᶠ .leftAct d .snd .snd F G = refl
hasBiWPFunctorStructure⋔ᶠ .rightAct c .fst {x = x} {y} = ⋔ᶠ→ᵣ c x y
hasBiWPFunctorStructure⋔ᶠ .rightAct c .snd .fst x = refl
hasBiWPFunctorStructure⋔ᶠ .rightAct c .snd .snd F G = refl

-- Functoriality of _⊠ᶠ_
hasBiWPFunctorStructure⊠ᶠ :
  hasBiWPFunctorStructure ⌈ 𝑭𝑨𝑴 ℓ₁ ⌉ ⌈ 𝑭𝑨𝑴 ℓ₁ ⌉ ⌈ 𝑭𝑨𝑴 ℓ₁ ⌉ _⊠ᶠ_
hasBiWPFunctorStructure⊠ᶠ .leftAct d .fst {y = y} = ⊠ᶠ→ₗ _ y d
hasBiWPFunctorStructure⊠ᶠ .leftAct d .snd .fst _ =
  ΣPathP (refl , (funExt (λ {(x , a) → funExt
    (elim∣inl x ↦ refl ∣inr x ↦ refl ∣push x ↦ λ _ → refl)})))
hasBiWPFunctorStructure⊠ᶠ .leftAct d .snd .snd F G =
  ΣPathP (refl , (funExt (λ {(x , a) → funExt
    (elim∣inl x ↦ refl ∣inr x ↦ refl ∣push x ↦ λ _ → refl)})))
hasBiWPFunctorStructure⊠ᶠ .rightAct c .fst {x = x} {y} = ⊠ᶠ→ᵣ c x y
hasBiWPFunctorStructure⊠ᶠ .rightAct c .snd .fst _ =
  ΣPathP (refl , (funExt (λ {(x , a) → funExt
    (elim∣inl x ↦ refl ∣inr x ↦ refl ∣push x ↦ λ _ → refl)})))
hasBiWPFunctorStructure⊠ᶠ .rightAct c .snd .snd F G =
  ΣPathP (refl , (funExt (λ {(x , a) → funExt
    (elim∣inl x ↦ refl ∣inr x ↦ refl ∣push x ↦ λ _ → refl)})))

-- associativity
assoc⊠ᶠ : ∀ {ℓ₃} (f : Fam ℓ₁) (g : Fam ℓ₂) (h : Fam ℓ₃)
  → ((f ⊠ᶠ g) ⊠ᶠ h) ≃Fam (f ⊠ᶠ (g ⊠ᶠ h))
assoc⊠ᶠ (A , B) (X , Y) (P , Q) .fst = Σ-assoc-≃
assoc⊠ᶠ (A , B) (X , Y) (P , Q) .snd _ =
  invEquiv (isoToEquiv joinAssocIso)

-- Formula describing the interaction between ⊠ᶠ and ⋔ᶠ
Iso-[[⊠ᶠ]-⋔ᶠ]-[⋔ᶠ-[⋔ᶠ]] : (A B C : Fam ℓ₁) → ((A ⊠ᶠ B) ⋔ᶠ C) ≃Fam (A ⋔ᶠ (B ⋔ᶠ C))
Iso-[[⊠ᶠ]-⋔ᶠ]-[⋔ᶠ-[⋔ᶠ]] (A , B) (X , Y) (C , D) =
  isoToEquiv fstIso , sndIso
  where
  -- This iso can be done by shuffling Σ's and Π's but it's quicker to
  -- just define it directly...
  fstIso : Iso Fam[ (A , B) ⊠ᶠ (X , Y) , (C , D) ]
               Fam[ (A , B) , (X , Y) ⋔ᶠ (C , D) ]
  fstIso .fun (f , p) =
      (λ a → (f ∘ (a ,_))
            , λ b y → p (a , b) (inr y))
     , λ a b x → (p (a , x) (inl b))
                , λ y → cong (p (a , x)) (sym (push (b , y)))
  fstIso .inv (f , p) =
     (λ {(a , x) → f a .fst x})
    , λ {(a , x) → rec∣inl w ↦ p a w x .fst
                       ∣inr w ↦ f a .snd x w
                       ∣push w ↦ sym (p a (fst w) x .snd (snd w))}
  fstIso .sec _ = refl
  fstIso .ret (f , p) = ΣPathP (refl
    , funExt λ {(a , x) →
      funExt (elim∣inl w ↦ refl
                   ∣inr w ↦ refl
                   ∣push w ↦ λ i _ → p _ (push w i))})

  -- abbreviations
  F : (fp : Fam[ ((A , B) ⊠ᶠ (X , Y)) , (C , D) ]) (a : A)
    → (B a → (x : X) → Const (fp .snd (a , x) ∘ inr))
  F (f , p) a b x .fst = p (a , x) (inl b)
  F (f , p) a b x .snd y = cong (p (a , x)) (sym (push (b , y)))

  G : (fp : Fam[ ((A , B) ⊠ᶠ (X , Y)) , (C , D) ]) (ax : A × X)
    → (B (fst ax) → Const (fp .snd ax ∘ inr))
  G (f , p) ax b .fst = p ax (inl b)
  G (f , p) ax b .snd y = cong (p ax) (sym (push (b , y)))

  sndIso : (fp : Fam[ ((A , B) ⊠ᶠ (X , Y)) , (C , D) ]) →
      ((ax : A × X) → Const (fp .snd ax))
    ≃ ((a : A) → Const (F fp a))
  sndIso (f , p) =
    ((ax : A × X) → Const (p ax))           ≃⟨ codomainEquivDep (uncurry codomEquiv) ⟩
    ((ax : A × X) → Const (G (f , p) ax))   ≃⟨ currying ⟩
    ((a : A) → Const (F (f , p) a)) ■
    where
    codomEquiv : (a : A) (x : X) → Const (p (a , x)) ≃ Const (G (f , p) (a , x))
    codomEquiv a x =
      Const (p (a , x))                                    ≃⟨ Σ-cong-equiv-snd main ⟩
      (Σ[ l ∈ D (f (a , x)) ]
        Σ[ r ∈ ((y : Y x) → p (a , x) (inr y) ≡ l) ]
          ((b : B a) → G (f , p) (a , x) b ≡ (l , r)))     ≃⟨ invEquiv Σ-assoc-≃ ⟩
      Const (G (f , p) (a , x)) ■
      where
      main : (l : D (f (a , x))) → (((j : join (B a) (Y x)) → p (a , x) j ≡ l))
                                  ≃ (Σ[ r ∈ ((y : Y x) → p (a , x) (inr y) ≡ l) ]
                                      ((b : B a) → G (f , p) (a , x) b ≡ (l , r)))
      main l =
        ((j : join (B a) (Y x)) → p (a , x) j ≡ l)                               ≃⟨ domEquivDep (isoToEquiv joinCommIso) ⟩
        ((j : join (Y x) (B a)) → p (a , x) (joinCommFun j) ≡ l)                 ≃⟨ isoToEquiv characJoinElim ⟩
        (Σ[ r ∈ ((y : Y x) → _) ] Σ[ t ∈ ((b : B a) → _) ]
         ((y : Y x) (b : B a) → Square _ _ _ _))                                 ≃⟨ Σ-cong-equiv-snd final ⟩
        (Σ[ r ∈ ((y : Y x) → p (a , x) (inr y) ≡ l) ]
          ((b : B a) → G (f , p) (a , x) b ≡ (l , r))) ■
          where
          flipEquiv : (b : B a)  (y : Y x) (l : D (f (a , x)))
            (r : p (a , x) (inr y) ≡ l) (t : p (a , x) (inl b) ≡ l)
            → Square r t (λ i → p (a , x) (push (b , y) (~ i))) refl
             ≃ Square (λ i → p (a , x) (push (b , y) (~ i))) r refl t
          flipEquiv b y = J> λ t → flipSquareEquiv

          final : (r : ((y : Y x) → p (a , x) (inr y) ≡ l))
            → (Σ[ t ∈ ((b : B a) → p (a , x) (inl b) ≡ l) ]
                   ((y : Y x) (b : B a) → Square _ _ _ _))
            ≃ (((b : B a) → G (f , p) (a , x) b ≡ (l , r)))
          final r =
            (Σ[ l ∈ _ ] ((y : Y x) (b : B a) → _))       ≃⟨ Σ-cong-equiv-snd (λ t → swapArgsEquiv) ⟩
            (Σ[ l ∈ _ ] ((b : B a) (y : Y x) → _))       ≃⟨ invEquiv (Σ-Π-≃ {A = B a}
                                                             {B = λ z → p (a , x) (inl z) ≡ l}
                                                             {C = λ b s → (y : Y x) → Square _ _ _ _}) ⟩
            ((b : B a) → Σ[ t ∈ _ ≡ _ ]
                           ((y : Y x) → Square _ _ _ _)) ≃⟨ codomainEquivDep (λ b → Σ-cong-equiv-snd
                                                                              λ t → compEquiv (codomainEquivDep
                                                                                     (λ y → flipEquiv b y l (r y) t))
                                                                                               funExtEquiv) ⟩
            ((b : B a) → Σ[ t ∈ _ ≡ _ ] PathP _ _ _)     ≃⟨ codomainEquivDep (λ b → ΣPath≃PathΣ) ⟩
            ((b : B a) → G (f , p) (a , x) b ≡ (l , r)) ■

    currying : ((ax : A × X) → Const (G (f , p) ax))
             ≃ ((a : A) → Const (F (f , p) a))
    currying =
      ((ax : A × X) → Const (G (f , p) ax))              ≃⟨ curryEquiv ⟩
      ((a : A) (x : X) → Const (G (f , p) (a , x)))      ≃⟨ codomainEquivDep main ⟩
      ((a : A) → Const (F (f , p) a)) ■
     where
     help : (a : A) (m : (x : X) → Const (p (a , x) ∘ inr))
       → (((x : X) (b : B a) → G (f , p) (a , x) b ≡ m x))
        ≃ (((b : B a) → F (f , p) a b ≡ m))
     help a m =
       (((x : X) (b : B a) → _))                         ≃⟨ swapArgsEquiv ⟩
       ((b : B a) (x : X) → G (f , p) (a , x) b ≡ m x)   ≃⟨ codomainEquivDep (λ b → funExtEquiv) ⟩
       ((b : B a) → F (f , p) a b ≡ m) ■

     main : (a : A) → ((x : X) → Const (G (f , p) (a , x))) ≃ Const (F (f , p) a)
     main a =
       ((x : X) → Const (G (f , p) (a , x)))                         ≃⟨ Σ-Π-≃ ⟩
       (Σ[ g ∈ ((x : X) → Const (p (a , x) ∘ inr)) ]
               ((x : X) (b : B a) → G (f , p) (a , x) b ≡ g x))      ≃⟨ Σ-cong-equiv-snd (help a) ⟩
       Const (F (f , p) a) ■
