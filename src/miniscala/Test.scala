package miniscala

import miniscala.Ast._
import miniscala.Interpreter._
import miniscala.TypeChecker._
import miniscala.parser.Parser.parse
import miniscala.AbstractMachine._
import miniscala.Compiler._

object Test132 {

  def main(args: Array[String]): Unit = {
    test("2 + 3", 5) //plus
    test("3 - 2", 1) //minus
    test("2 * 3", 6) //multiplication
    test("4 / 2", 2) //division

    //negation
    test("-(-2)", 2)
    test("-2 * 4", -8)
    test("-2 * 4", -8)
    test("-2 + 4", 2)

    test("2 + 3 * 2", 8) //plus and multiplication

    //Eq
    test("2 == 2", 1)
    test("2 == 3", 0)
    //Lt
    test("2 < 3", 1)
    test("2 < 2", 0)
    //Leq
    test("2 <= 2", 1)
    test("2 <= 3", 1)
    test("3 <= 2", 0)
    //And
    test("true & true", 1)
    test("true & false", 0)
    //Or
    test("false | true", 1)
    test("false | false", 0)
    //Not
    test("!false", 1)
    test("!true", 0)
    //Blockexp
    test("{ val x = 10; x }", 10)
    test("{ val y = 10; { val y = 5; y } + y }", 15)

    println("All tests passed successfully!")
  }

  def test(prg: String, result: Int): Unit = {
    assert(execute(compile(parse(prg)), Nil) == result)
  }



}

object Test112 {

  def main(args: Array[String]): Unit = {
    testValFail("""{ var z = null; z.f }""")
    testVal("""{ class C() { }; { var x: C = null; x = new C() } }""".stripMargin, TupleVal(List[Val]()))
    testVal("""{ class C() { }; { var x: C = new C(); x = null } }""".stripMargin, TupleVal(List[Val]()))
    // <-- add more test cases here

    testVal("""    {
              |      val x: Int = 42;
              |      val y: Float = x;
              |      class C() {};
              |      {
              |        var z: C = null;
              |        z = null
              |      }
              |    }""".stripMargin, TupleVal(List[Val]()))

    println("All tests passed successfully!")
  }

  def testVal(prg: String, value: Val, env: Env = Map(), cenv: ClassEnv = Map(), sto: Sto = Map()): Unit = {
    val (res, _) = eval(parse(prg), env, cenv, sto)
    assert(res == value)
  }

  def testValFail(prg: String, env: Env = Map(), cenv: ClassEnv = Map(), sto: Sto = Map()): Unit = {
    try {
      eval(parse(prg), env, cenv, sto)
      assert(false)
    } catch {
      case _: InterpreterError => assert(true)
    }
  }

}

  object Test111 {

    def main(args: Array[String]): Unit = {
      testTypeFail("{ class A() {}; new B() }")
      testTypeFail("{ val X = 42; new X() }")
      testTypeFail("{ class C(i: Int) { }; new C(1 - \"hello\") }")
      testTypeFail("{ class C(i: Int) { }; new C(1, 2) }")
      testTypeFail("42.f")
      testTypeFail("{ class C() { def f(x: Int): Int = 42 }; { val o = new C(); o.g } }")
      testTypeFail("{ class C(i) { } } ")
      testTypeFail("{ class C(i) { 1 - \"hello\" } } ")
      testTypeFail("{ class A() {}; class B() {}; { val x: A = new B() }}")
      testTypeFail(
        """
          |    { class C() { val a: Boolean = false };
          |      {
          |        {
          |          var x: C = new C();
          |          class C() { val a: Int = 42 };
          |          { val y: C = x }
          |        }
          |      }
          |    }""".stripMargin)
      testTypeFail(
        """
          |    { class C() { val a: Boolean = false };
          |      {
          |        {
          |          var x: C = new C();
          |          class C() { val a: Int = 42 };
          |          { x = new C() }
          |        }
          |      }
          |    }""".stripMargin)

      testType(
        """{ class A() { };
          |  class B() { var x: A = new A() } }""".stripMargin, unitType)
      testType(
        """{
          |  class Counter(init: Int) {
          |    var c: Int = init;
          |    def getValue(): Int = c;
          |    def inc(): Unit = { c = c + 1 }
          |  };
          |  {
          |    val x = new Counter(3);
          |    x.inc();
          |    x.inc();
          |    x.getValue()
          |  }
          |}""".stripMargin, IntType())
      testType("{ class A(x: Int) { val x: Int = x }; { def f(a: A): Int = a.x; f(new A(2)) } }", IntType())
      testType("{ class A() { }; class B(a: A) { }; new B(new A()) ; {} }", unitType)
      testType("{ class A(x: Int) { new A(x-1) }; new A(10); {} }", unitType)
      testType("{ class A(b: B) { new B() }; class B() { }; {} }", unitType)

      println("All tests passed successfully!")
    }

    def testType(prg: String, out: Type, tenv: TypeEnv = Map(), ctenv: ClassTypeEnv = Map()): Unit = {
      assert(typeCheck(parse(prg), tenv, ctenv) == out)
    }

    def testTypeFail(prg: String): Unit = {
      try {
        typeCheck(parse(prg), Map(), Map())
        assert(false)
      } catch {
        case _: TypeError => assert(true)
      }
    }
  }

object Test95 {

  def main(args: Array[String]): Unit = {
    test("{ def f(x: Int): Int = x; f(2) }", IntVal(2), IntType())
    testFail("{ def f(x: Int): Int = x; f(2, 3) }")
    testVal("{ var z: Int = 0; { var t: Int = x; while (y <= t) { z = z + 1; t = t - y }; z } }", IntVal(3), Map("x" -> IntVal(17), "y" -> IntVal(5)))
    testType("{ var z: Int = 0; { var t: Int = x; while (y <= t) { z = z + 1; t = t - y }; z } }", IntType(), Map("x" -> IntType(), "y" -> IntType()))
    testVal("{ var x: Int = 0; def inc(): Int = { x = x + 1; x }; inc(); inc() }", IntVal(2))
    testType("{ var x: Int = 0; def inc(): Int = { x = x + 1; x }; inc(); inc() }", IntType())
    testVal("""{ def make(a: Int): Int => Int = {
              |    var c: Int = a;
              |    def add(b: Int): Int = { c = c + b; c };
              |    add
              |  };
              |  { val c1 = make(100);
              |    val c2 = make(1000);
              |    c1(1) + c1(2) + c2(3) } }""".stripMargin, IntVal(101 + 103 + 1003))
    testVal("if (!false) -1 else 2", IntVal(-1), Map())

    // <-- add more test cases here

    println("All tests passed successfully!")
  }

  def test(prg: String, rval: Val, rtype: Type): Unit = {
    testVal(prg, rval)
    testType(prg, rtype)
  }

  def testFail(prg: String): Unit = {
    testValFail(prg)
    testTypeFail(prg)
  }

  def testVal(prg: String, value: Val, env: Env = Map(), cenv: ClassEnv = Map[Id, Constructor](), sto: Sto = Map()): Unit = {
    val (res, _) = eval(parse(prg), env, cenv, sto)
    assert(res == value, res)
  }

  def testType(prg: String, out: Type, tenv: TypeEnv = Map[Id, Type](), ctenv: ClassTypeEnv = Map[Id, StaticClassType]()): Unit = {
    assert(typeCheck(parse(prg), tenv, ctenv) == out)
  }

  def testValFail(prg: String,env: Env = Map[Id, Val](), cenv: ClassEnv = Map[Id, Constructor](), sto: Sto = Map[Loc, Val]()): Unit = {
    try {
      eval(parse(prg), env, cenv, sto)
      assert(false)
    } catch {
      case _: InterpreterError => assert(true)
    }
  }

  def testTypeFail(prg: String): Unit = {
    try {
      typeCheck(parse(prg), Map[Id, Type](), Map[Id, StaticClassType]())
      assert(false)
    } catch {
      case _: TypeError => assert(true)
    }
  }
}

object Test68 {

  def main(args: Array[String]): Unit = {
    testVal("{def f(x) = x; f(2)}", IntVal(2))
    testTypeFail("{def f(x) = x; f(2)}")

    println("All tests passed successfully!")
  }

  def test(prg: String, rval: Val, rtype: Type): Unit = {
    testVal(prg, rval)
    testType(prg, rtype)
  }

  def testFail(prg: String): Unit = {
    testValFail(prg)
    testTypeFail(prg)
  }

  def testVal(prg: String, value: Val, env: Env = Map(), cenv: ClassEnv = Map[Id, Constructor](), sto: Sto = Map()): Unit = {
    val (res, _) = eval(parse(prg), env, cenv, sto)
    assert(res == value, res)
  }

  def testType(prg: String, out: Type, tenv: TypeEnv = Map[Id, Type](), ctenv: ClassTypeEnv = Map[Id, StaticClassType]()): Unit = {
    assert(typeCheck(parse(prg), tenv, ctenv) == out)
  }

  def testValFail(prg: String,env: Env = Map[Id, Val](), cenv: ClassEnv = Map[Id, Constructor](), sto: Sto = Map[Loc, Val]()): Unit = {
    try {
      eval(parse(prg), env, cenv, sto)
      assert(false)
    } catch {
      case _: InterpreterError => assert(true)
    }
  }

  def testTypeFail(prg: String): Unit = {
    try {
      typeCheck(parse(prg), Map[Id, Type](), Map[Id, StaticClassType]())
      assert(false)
    } catch {
      case _: TypeError => assert(true)
    }
  }
}

object Test49 {

  def main(args: Array[String]): Unit = {
    test("{def f(x: Int): Int = x; f(2)}", IntVal(2), IntType())
    testFail("{def f(x: Int): Int = x; f(2, 3)}")
    test("{def f(x: Int): Int = x*x; f(2)}", IntVal(4), IntType())
    testFail("{def f(x: Int, y: Int): Int = x; f(2)}")
    test("{def f(x: Int, y: Int): Int = x+y; f(2,5)}", IntVal(7), IntType())
    testFail("{def f(x: Int): String = x; f(2)}")
    test("{def f(x: Int, y: Int, z: Int): Int = x-y-z; f(10,5,2)}", IntVal(3), IntType())
    testFail("{def f(x: Int, y: Int): Int = x+y; f(2)}")

    println("All tests passed successfully!")
  }

  def test(prg: String, rval: Val, rtype: Type): Unit = {
    testVal(prg, rval)
    testType(prg, rtype)
  }

  def testFail(prg: String): Unit = {
    testValFail(prg)
    testTypeFail(prg)
  }

  def testVal(prg: String, value: Val, env: Env = Map(), cenv: ClassEnv = Map[Id, Constructor](), sto: Sto = Map()): Unit = {
    val (res, _) = eval(parse(prg), env, cenv, sto)
    assert(res == value, res)
  }

  def testType(prg: String, out: Type, tenv: TypeEnv = Map[Id, Type](), ctenv: ClassTypeEnv = Map[Id, StaticClassType]()): Unit = {
    assert(typeCheck(parse(prg), tenv, ctenv) == out)
  }

  def testValFail(prg: String,env: Env = Map[Id, Val](), cenv: ClassEnv = Map[Id, Constructor](), sto: Sto = Map[Loc, Val]()): Unit = {
    try {
      eval(parse(prg), env, cenv, sto)
      assert(false)
    } catch {
      case _: InterpreterError => assert(true)
    }
  }

  def testTypeFail(prg: String): Unit = {
    try {
      typeCheck(parse(prg), Map[Id, Type](), Map[Id, StaticClassType]())
      assert(false)
    } catch {
      case _: TypeError => assert(true)
    }
  }
}

//useless
/*object Test89 {
  def main(args: Array[String]): Unit = {
    println(Unparser.unparse(Lambda.encode(parse("if (!false) 1 else 2"))))
    println(Unparser.unparse(Lambda.encode(parse("0 + 1 == 0"))))
    //missing 80(e).s
  }
}*/

/*object Test57 {
  def main(args: Array[String]): Unit = {
    Week5.testMergeSort()
    val list1: IntList = Cons(1, Cons(2, Nil))
    val list2: IntList = Cons(2, Cons(1, Nil))
    val list3: IntList = Cons(1, Cons(3, Nil))
    assert(Week5.permuted(list1, list2))
    assert(!Week5.permuted(list1, list3))
    println("All permuted test completed")
  }
}
*/