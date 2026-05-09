package anthill.smtgen

/** v0 acceptance for WI-213: discharge `comm_delay_max ≤ 0.1` for an
  * lf1-shaped KB. Mirrors
  * `rustland/anthill-smt-gen/tests/comm_delay_test.rs`.
  */
class CommDelayTest extends munit.FunSuite:

  /** Trimmed safety spec — enough for the comm_delay_max obligation.
    * Field consts come from the LinkParameters / KinematicAssumptions
    * facts; the rule body's five linear ops bind ?tau = T_prop +
    * T_trans + T_c.
    */
  private val source = """
    namespace test.smt_gen.lf1
      import anthill.prelude.{Float, Int}
      import anthill.prelude.Numeric.{add, mul}
      import anthill.prelude.Float.{div}

      export LinkParameters, KinematicAssumptions, comm_delay_max

      entity LinkParameters(
        range_max:    Float,
        signal_speed: Float,
        baud_rate:    Float,
        byte_size:    Int,
        packet_size:  Int
      )

      entity KinematicAssumptions(
        leader_speed_max:    Float,
        follower_speed_max:  Float,
        control_period:      Float,
        sensor_period:       Float
      )

      rule comm_delay_max: comm_delay_max(?tau)
        :- LinkParameters(range_max: ?r,
                          signal_speed: ?c,
                          baud_rate: ?br,
                          byte_size: ?bs,
                          packet_size: ?ps),
           KinematicAssumptions(control_period: ?tc),
           ?prop  = div(?r, ?c),
           ?bits  = mul(?ps, ?bs),
           ?trans = div(?bits, ?br),
           ?sum1  = add(?prop, ?trans),
           ?tau   = add(?sum1, ?tc)

      fact LinkParameters(
        range_max:    100.0,
        signal_speed: 300000000.0,
        baud_rate:    1000000.0,
        byte_size:    8,
        packet_size:  32
      )

      fact KinematicAssumptions(
        leader_speed_max:    8.0,
        follower_speed_max:  8.0,
        control_period:      0.032,
        sensor_period:       0.008
      )
    end
  """

  private def lf1SafetyKb() = Common.loadKbWith(source)

  private val obligation =
    Obligation("test.smt_gen.lf1.comm_delay_max", 0.1)

  test("comm_delay_max emits a well-formed SMT-LIB doc") {
    val kb = lf1SafetyKb()
    val smt = SmtGen.emitObligation(kb, obligation) match
      case Right(s) => s
      case Left(e)  => fail(s"emit failed: ${e.message}")

    assert(smt.contains("(set-logic QF_LRA)"), s"missing logic declaration:\n$smt")
    assert(smt.contains("(define-fun range_max () Real 100.0)"),
      s"missing range_max field-const:\n$smt")
    assert(smt.contains("(define-fun control_period () Real 0.032)"),
      s"missing control_period field-const:\n$smt")
    assert(smt.contains("(define-fun var_") && smt.contains("() Real "),
      s"missing body define-fun for the result var:\n$smt")
    assert(smt.contains("(assert (not (<= var_") && smt.contains(" 0.1)))"),
      s"missing upper-bound obligation assertion:\n$smt")
    assert(smt.contains("(check-sat)"), s"missing (check-sat):\n$smt")
  }

  test("comm_delay_max round-trips through z3 to unsat".tag(munit.Tag("requires-z3"))) {
    assume(Z3Runner.available, "z3 not on $PATH; skipping")
    val kb = lf1SafetyKb()
    val smt = SmtGen.emitObligation(kb, obligation) match
      case Right(s) => s
      case Left(e)  => fail(s"emit failed: ${e.message}")
    val verdict = Z3Runner.run("comm_delay", smt)
    assert(verdict.startsWith("unsat"),
      s"expected `unsat` (comm_delay_max ≤ 0.1 must hold for these constants), got:\n$verdict")
  }

  test("config overrides logic and emits timeout") {
    val kb = lf1SafetyKb()
    val cfg = ProofConfig(logic = Some("QF_NRA"), timeoutMs = Some(5000))
    val smt = SmtGen.emitObligationWith(kb, obligation, cfg) match
      case Right(s) => s
      case Left(e)  => fail(s"emit failed: ${e.message}")
    assert(smt.contains("(set-logic QF_NRA)"),
      s"expected logic override to QF_NRA:\n$smt")
    assert(smt.contains("(set-option :timeout 5000)"),
      s"expected timeout 5000:\n$smt")
  }

  test("comm_delay_max emits arith in correct SMT-LIB prefix order") {
    val kb = lf1SafetyKb()
    val smt = SmtGen.emitObligation(kb, obligation) match
      case Right(s) => s
      case Left(e)  => fail(s"emit failed: ${e.message}")
    // Body should contain prefix-form arithmetic, e.g. `(+ ... ...)`,
    // `(/ range_max signal_speed)`, etc.
    assert(smt.contains("(/ range_max signal_speed)"),
      s"expected `(/ range_max signal_speed)` in body:\n$smt")
    assert(smt.contains("(* packet_size byte_size)"),
      s"expected `(* packet_size byte_size)` in body:\n$smt")
  }
