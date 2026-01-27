import Lean.Meta

initialize toPolynomialSimpSet : Lean.Meta.SimpExtension ←
  Lean.Meta.registerSimpAttr `toPolynomialSimp "lemmas for toPolynomial"
