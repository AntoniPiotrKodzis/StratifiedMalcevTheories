{-# OPTIONS --cubical --guardedness #-}

module BP where

  open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.Data.Sigma
  open import Cubical.Data.Unit using (Unit; tt)

  ----------------------------------------------------------------------
  -- 0. Minimal universe tower (placeholder).
  -- Replace/redirect this module to your own Stratification module later.
  ----------------------------------------------------------------------

  module Stratification where
    HeightLevel : ℕ → Level
    HeightLevel zero    = lzero
    HeightLevel (suc n) = lsuc (HeightLevel n)

  ----------------------------------------------------------------------
  -- 1. A tiny ∞-category interface (hom-types can be higher types)
  ----------------------------------------------------------------------

  record ∞Cat (ℓObj ℓHom : Level) : Type (lsuc (ℓObj ⊔ ℓHom)) where
    field
      Obj   : Type ℓObj
      Hom   : Obj → Obj → Type ℓHom

      id    : (X : Obj) → Hom X X
      _⋆_   : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z

      idl   : {X Y : Obj} (f : Hom X Y) → (id Y ⋆ f) ≡ f
      idr   : {X Y : Obj} (f : Hom X Y) → (f ⋆ id X) ≡ f
      assoc : {W X Y Z : Obj} (h : Hom Y Z) (g : Hom X Y) (f : Hom W X) →
              (h ⋆ (g ⋆ f)) ≡ ((h ⋆ g) ⋆ f)

  open ∞Cat public

  ----------------------------------------------------------------------
  -- 2. Small coproducts indexed by a type in universe level κ
  ----------------------------------------------------------------------

  record HasCoproducts {ℓObj ℓHom : Level} (P : ∞Cat ℓObj ℓHom) (κ : Level)
    : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ)) where
    field
      Coprod : {I : Type κ} → (I → Obj P) → Obj P
      ι      : {I : Type κ} {A : I → Obj P} → (i : I) → Hom P (A i) (Coprod A)

      -- Universal property as an equivalence of mapping types:
      coprod-UP :
        {I : Type κ} {A : I → Obj P} {X : Obj P} →
        Hom P (Coprod A) X ≃ ((i : I) → Hom P (A i) X)

  open HasCoproducts public

  ----------------------------------------------------------------------
  -- 3. Simplicial objects (abstract “shape”; refine later with Δᵒᵖ)
  ----------------------------------------------------------------------

  record Simp {ℓ : Level} (A : Type ℓ) : Type (lsuc ℓ) where
    field
      Objₙ : ℕ → A

  open Simp public

  ----------------------------------------------------------------------
  -- 4. BP I Interface kernel
  ----------------------------------------------------------------------

  record BPInterface (ℓObj ℓHom κ ℓSpc : Level)
    : Type (lsuc (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))) where

    field
      -- Underlying pretheory data
      P       : ∞Cat ℓObj ℓHom
      coprods : HasCoproducts P κ

      -- Nonbounded models (abstract carrier + morphisms)
      ModelNb : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
      HomNb   : ModelNb → ModelNb → Type (lsuc (ℓObj ⊔ ℓHom ⊔ ℓSpc))

      -- Evaluation at objects of P
      eval    : ModelNb → Obj P → Type (ℓSpc ⊔ κ)
      evalMap : {X Y : ModelNb} → HomNb X Y → (p : Obj P) → eval X p → eval Y p

      -- “Small/bounded” predicate (BP I Def 3.1.6)
      isSmall : ModelNb → Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))

      -- Bounded models as a sub-type with inclusion
      Model     : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
      incl      : Model → ModelNb
      inclSmall : (X : Model) → isSmall (incl X)

      -- Restricted Yoneda (representables)
      ν      : Obj P → ModelNb
      νSmall : (p : Obj P) → isSmall (ν p)

      ----------------------------------------------------------------
      -- Space-level simplicial technology
      ----------------------------------------------------------------

      isKanSpc : Simp (Type (ℓSpc ⊔ κ)) → Type (lsuc (ℓSpc ⊔ κ))
      ∣_∣Spc   : Simp (Type (ℓSpc ⊔ κ)) → Type (ℓSpc ⊔ κ)

      -- “Kan levelwise realizations commute with products”
      realize-Π :
        {I : Type κ} (X : I → Simp (Type (ℓSpc ⊔ κ))) →
        ((i : I) → isKanSpc (X i)) →
        (∣ record { Objₙ = λ n → (i : I) → Objₙ (X i) n } ∣Spc)
          ≃ ((i : I) → ∣ X i ∣Spc)

      ----------------------------------------------------------------
      -- Čech nerves + effective epimorphisms (space-level)
      ----------------------------------------------------------------

      Cech     : {X Y : Type (ℓSpc ⊔ κ)} → (f : X → Y) → Simp (Type (ℓSpc ⊔ κ))
      cech-aug : {X Y : Type (ℓSpc ⊔ κ)} (f : X → Y) → (∣ Cech f ∣Spc → Y)

      isEffEpiSpc : {X Y : Type (ℓSpc ⊔ κ)} → (X → Y) → Type (lsuc (ℓSpc ⊔ κ))

      effEpi⇔cech :
        {X Y : Type (ℓSpc ⊔ κ)} (f : X → Y) →
        isEffEpiSpc f ≃ isEquiv (cech-aug f)

      effEpi⇒cechKan :
        {X Y : Type (ℓSpc ⊔ κ)} (f : X → Y) → isEffEpiSpc f → isKanSpc (Cech f)

      ----------------------------------------------------------------
      -- Model-level simplicial objects + realizations
      ----------------------------------------------------------------

      SimpNb : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
      simpAt : SimpNb → ℕ → ModelNb
      ∣_∣Nb  : SimpNb → ModelNb

      eval-realize :
        (X : SimpNb) (p : Obj P) →
        eval (∣ X ∣Nb) p ≃ ∣ record { Objₙ = λ n → eval (simpAt X n) p } ∣Spc

      isKanLevelwise   : SimpNb → Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
      isSplitLevelwise : SimpNb → Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))

      -- BP I Prop 3.1.7(2)(3) closure packaged as inhabitance
      closed-realizeKan   : (X : SimpNb) → isKanLevelwise X → Unit
      closed-realizeSplit : (X : SimpNb) → isSplitLevelwise X → Unit

      -- BP I Cor 3.1.8: Kan detected levelwise
      isKanNb      : SimpNb → Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
      kan-detected : (X : SimpNb) → isKanNb X ≃ isKanLevelwise X

      -- BP I §3.5 hook (placeholder)
      isPresentable : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))

  -- (No global open of BPInterface: avoid overloaded projection ambiguity.)

  ----------------------------------------------------------------------
  -- 5. Background II: BP I §3.1–§3.5 (formal spine)
  ----------------------------------------------------------------------

  module BackgroundII
    {ℓObj ℓHom κ ℓSpc : Level} (I : BPInterface ℓObj ℓHom κ ℓSpc) where

    -- Avoid overloaded-projection ambiguity by hiding the record fields
    -- and reintroducing them as explicit aliases.
    open BPInterface I hiding
      ( ModelNb ; HomNb ; SimpNb
      ; isKanLevelwise ; isSplitLevelwise
      ; closed-realizeKan ; closed-realizeSplit
      ; isKanNb ; kan-detected
      )

    ModelNb₀ : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
    ModelNb₀ = BPInterface.ModelNb I

    HomNb₀ : ModelNb₀ → ModelNb₀ → Type (lsuc (ℓObj ⊔ ℓHom ⊔ ℓSpc))
    HomNb₀ = BPInterface.HomNb I

    SimpNb₀ : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
    SimpNb₀ = BPInterface.SimpNb I

    isKanLevelwise₀ : SimpNb₀ → Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
    isKanLevelwise₀ = BPInterface.isKanLevelwise I

    isSplitLevelwise₀ : SimpNb₀ → Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
    isSplitLevelwise₀ = BPInterface.isSplitLevelwise I

    closed-realizeKan₀ : (X : SimpNb₀) → isKanLevelwise₀ X → Unit
    closed-realizeKan₀ = BPInterface.closed-realizeKan I

    closed-realizeSplit₀ : (X : SimpNb₀) → isSplitLevelwise₀ X → Unit
    closed-realizeSplit₀ = BPInterface.closed-realizeSplit I

    isKanNb₀ : SimpNb₀ → Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
    isKanNb₀ = BPInterface.isKanNb I

    kan-detected₀ : (X : SimpNb₀) → isKanNb₀ X ≃ isKanLevelwise₀ X
    kan-detected₀ = BPInterface.kan-detected I


    -- A “pretheory” in this interface: category + κ-coproduct structure
    Pretheory : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ))
    Pretheory = Σ[ P' ∈ ∞Cat ℓObj ℓHom ] HasCoproducts P' κ

    -- BP I Prop 3.1.7(2): closure under Kan-levelwise realizations
    Prop3-1-7-2 : (X : SimpNb₀) → isKanLevelwise₀ X → Unit
    Prop3-1-7-2 = closed-realizeKan₀

    -- BP I Prop 3.1.7(3): closure under split realizations
    Prop3-1-7-3 : (X : SimpNb₀) → isSplitLevelwise₀ X → Unit
    Prop3-1-7-3 = closed-realizeSplit₀

    -- BP I Cor 3.1.8: Kan detected levelwise
    Cor3-1-8 : (X : SimpNb₀) → isKanNb₀ X ≃ isKanLevelwise₀ X
    Cor3-1-8 = kan-detected₀

    -- Extension bundles for the rest of BP I:
    record SliceIdemExtension : Type (lsuc (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))) where
      field
        SlicePretheory : (X : ModelNb₀) → Pretheory
        SliceModelsNb  : (X : ModelNb₀) → Unit
        IdemCompletion : Pretheory → Pretheory
        IdemModelsEq   : (P0 : Pretheory) → Unit

    record TruncConnExtension : Type (lsuc (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))) where
      field
        isTrunc : ℕ → {A B : Type (ℓSpc ⊔ κ)} → (A → B) → Type (lsuc (ℓSpc ⊔ κ))
        isConn  : ℕ → {A B : Type (ℓSpc ⊔ κ)} → (A → B) → Type (lsuc (ℓSpc ⊔ κ))

        isTruncatedMap  : ℕ → {X Y : ModelNb₀} → HomNb₀ X Y → Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
        isConnectiveMap : ℕ → {X Y : ModelNb₀} → HomNb₀ X Y → Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))

        LevelwiseCriterion :
          (n : ℕ) {X Y : ModelNb₀} (f : HomNb₀ X Y) →
          (isTruncatedMap n f ≃ ((p : Obj P) → isTrunc n (evalMap f p))) ×
          (isConnectiveMap n f ≃ ((p : Obj P) → isConn  n (evalMap f p)))

        HigherImageFactorization : (n : ℕ) → Unit

    record FreeResolutionExtension : Type (lsuc (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))) where
      field
        Cond1 : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
        Cond2 : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
        Cond3 : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))

        Lem3-4-1 : Σ[ e12 ∈ (Cond1 ≃ Cond2) ] (Cond2 ≃ Cond3)

        Thm3-4-2 : Unit
        Cor3-4-3 : Unit
        Cor3-4-4 : Unit

    record KappaBoundedExtension : Type (lsuc (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))) where
      field
        KappaAryTheory : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ))
        KappaAccessibleLocalization : Unit

        isKappaBounded : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ))
        isBounded      : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ))

        Thm3-5-10 : Unit
        Cor3-5-11 : isBounded ≃ isPresentable
        Warn3-5-12 : Unit

  ----------------------------------------------------------------------
  -- 6. Background III: universe stratification scaffold
  ----------------------------------------------------------------------

  module BackgroundIII where
    open Stratification

    -- Family of universes indexed by height.
    -- Note: In predicative Agda there is no single internal universe "Uω"
    -- that literally contains all U_n (the levels grow with n).  Instead we
    -- keep the family (U n) and express ω-stage bounds by Σ[ n ∈ ℕ ] ...
    U : (n : ℕ) → Type (lsuc (HeightLevel n))
    U n = Type (HeightLevel n)

    record UniverseBounded {ℓObj ℓHom κ ℓSpc : Level}
      (I : BPInterface ℓObj ℓHom κ ℓSpc)
      : Type (lsuc (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))) where

      private
        ModelNb₀ : Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
        ModelNb₀ = BPInterface.ModelNb I

        isSmall₀ : ModelNb₀ → Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))
        isSmall₀ = BPInterface.isSmall I

      field
        InU : (n : ℕ) → ModelNb₀ → Type (lsuc (ℓObj ⊔ ℓHom ⊔ κ ⊔ ℓSpc))

        bounded⇒finiteStage :
          (X : ModelNb₀) → isSmall₀ X → Σ[ n ∈ ℕ ] InU n X

      -- ω-stage bound: “exists a finite stage n”
      bounded⇒ωStage :
        (X : ModelNb₀) → isSmall₀ X → Σ[ n ∈ ℕ ] InU n X
      bounded⇒ωStage = bounded⇒finiteStage
