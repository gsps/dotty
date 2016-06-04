package dotty.tools.dotc

import leon.purescala.Common.{Identifier => LeonIdentifier, FreshIdentifier => LeonFreshIdentifier}

package object liquidtyper {

  type Identifier     = LeonIdentifier
  val FreshIdentifier = LeonFreshIdentifier

  val SubjectVarName        = core.Names.termName("v")
  val FreshQualifierPrefix  = "Ⲕ" //"kappa"

}
