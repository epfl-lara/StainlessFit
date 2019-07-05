import stainless.lang._
import stainless.collection._
import stainless.annotation._

object verified {

  def test = {
    1 + 1 == 2
  }.holds

}

