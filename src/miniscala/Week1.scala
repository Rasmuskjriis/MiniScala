package miniscala

import miniscala.Unparser.unparse
import miniscala.Ast._
import miniscala.parser.Parser

object Week1 {
  def main(args: Array[String]): Unit = {

    val a1 = BinOpExp(IntLit(2), MinusBinOp(), IntLit(10))
    val a2 = Parser.parse("2-10")
    println("Invoking toString on the AST gives: "+a2)
    println("The ASTs are equal: "+(a1==a2))

    val p = "1+4*(-1+4)"
    assert(Parser.parse(unparse(Parser.parse(p))) == Parser.parse(p))
  }

}
