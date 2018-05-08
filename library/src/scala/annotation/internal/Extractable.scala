package scala.annotation.internal

import scala.annotation.Annotation

/** An annotation to convey what tree to extract for a given symbol.
 *  @param body  A RefTree representing the precise body of the symbol.
 */
class Extractable(body: Any) extends Annotation {

}
