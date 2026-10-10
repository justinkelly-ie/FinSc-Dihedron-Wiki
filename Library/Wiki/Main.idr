module Wiki.Main

import QuickCheck
import Data.String
import Wiki.Dihedrons_And_Infinitesimals
import Wiki.Product_And_Chain_Rules
import Wiki.Finite_Field_Calculus
import Wiki.QuantumMechanicsAlgebra
import Language.Reflection

%default total

public export
%macro
auditInvariant : (prop : Bool) -> Elab (prop = True)
auditInvariant True = pure Refl
auditInvariant False = fail "Compile-time invariant audit failed!"

-- Compile-Time Invariant Audits (Rule 01)
0 auditSpinCommutatorProof : Wiki.QuantumMechanicsAlgebra.prop_spinCommutator = True
auditSpinCommutatorProof = Refl

0 auditDiracGamma0Proof : Wiki.QuantumMechanicsAlgebra.prop_diracGamma0Audit = True
auditDiracGamma0Proof = Refl

0 auditDiracQuadranceProof : Wiki.QuantumMechanicsAlgebra.prop_diracQuadranceAudit = True
auditDiracQuadranceProof = Refl

markdownTable : List (String, String, QCRes) -> String
markdownTable results =
  let header = "| Test | Description | Status | Details |\n|------|-------------|--------|---------|\n"
      rows = concat $ map formatRow results
  in header ++ rows
  where
    formatRow : (String, String, QCRes) -> String
    formatRow (name, desc, res) =
      let statusStr = case pass res of
                        Nothing => "❓ Unknown"
                        Just True => "✅ PASS"
                        Just False => "❌ FAIL"
      in "| " ++ name ++ " | " ++ statusStr ++ " | " ++ trim (msg res) ++ " |\n"

main : IO ()
main = do
  putStrLn "Starting FinSc-Dihedron-Wiki QuickCheck Suite...\n"
  putStrLn "Compile-Time Elaborator Reflection Audits (Rule 01):"
  putStrLn "  - Spin-1/2 Commutator Invariant: PASSED ✅ (Refl)"
  putStrLn "  - Dirac Gamma-0 Square Identity: PASSED ✅ (Refl)"
  putStrLn "  - Dirac Dihedron Quadrance Equivalence: PASSED ✅ (Refl)\n"
  
  putStrLn "Running Test 1: Subalgebra Metric Signatures"
  let res1 = quickCheck Wiki.Dihedrons_And_Infinitesimals.prop_subalgebraSignatures

  putStrLn "Running Test 2: Dual Derivative Theorem"
  let res2 = quickCheck Wiki.Dihedrons_And_Infinitesimals.prop_dualDerivativeTheorem

  putStrLn "Running Test 3: Algebraic Product Rule"
  let res3 = quickCheck Wiki.Product_And_Chain_Rules.prop_productRuleAlgebraic

  putStrLn "Running Test 4: Tangent Vector Readout"
  let res4 = quickCheck Wiki.Finite_Field_Calculus.prop_tangentVectorReadout

  putStrLn "Running Test 5: Pauli Anti-Commutativity Law"
  let res5 = quickCheck Wiki.QuantumMechanicsAlgebra.qc_pauliAntiCommutation

  putStrLn "Running Test 6: Spin-1/2 Commutator Law"
  let res6 = quickCheck Wiki.QuantumMechanicsAlgebra.qc_spinCommutator

  putStrLn "Running Test 7: Blue Phase Quadrance Invariance"
  let res7 = quickCheck Wiki.QuantumMechanicsAlgebra.qc_bluePhaseQuadranceInvariance

  putStrLn "Running Test 8: Monadic Feynman Path Propagator Composition"
  let res8 = quickCheck Wiki.QuantumMechanicsAlgebra.qc_monadicPathBinding

  putStrLn "Running Test 9: Dirac Spinor Clifford Cℓ_{1,3}(ℤ) & QuadStream Projection"
  let res9 = quickCheck Wiki.QuantumMechanicsAlgebra.qc_diracCliffordAlgebra

  let tableStr = markdownTable [
        ("Subalgebra Signatures", "Verifies Blue, Red, Green metric quadrances.", res1),
        ("Dual Derivative Theorem", "Verifies exact derivative readout via dual complex numbers.", res2),
        ("Algebraic Product Rule", "Verifies algebraic product rule for PolyNumbers.", res3),
        ("Tangent Vector Readout", "Verifies tangent vector calculation for semi-cubical parabola.", res4),
        ("Pauli Anti-Commutativity", "Verifies Pauli ZX = -XZ anti-commutation law on discrete dihedrons.", res5),
        ("Spin-1/2 Commutator", "Verifies [i, j] = 2k spin algebra commutator law.", res6),
        ("Blue Quadrance Invariance", "Verifies exact energy/norm conservation under U(1) blue rotations.", res7),
        ("Monadic Path Binding", "Verifies monadic propagator composition (>>=) across discrete paths.", res8),
        ("Dirac Clifford & QuadStream", "Verifies Dirac γ^0, spinor quadrance, and QuadStream multiset projection.", res9)
      ]

  putStrLn "\n--- Test Results ---"
  putStrLn tableStr
  putStrLn "FinSc-Dihedron-Wiki tests complete!"
