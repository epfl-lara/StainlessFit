package stainlessfit
package core
package typechecker

import core.trees._

import util.Utils._
import util.RunContext
import parser.FitParser

import Derivation._
import TypeOperators._

trait ScalaDepRules {

  implicit val rc: RunContext

  
}
