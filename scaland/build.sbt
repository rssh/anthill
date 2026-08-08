val scala3Version = "3.8.4"

lazy val root = project
  .in(file("."))
  .aggregate(core, anthillScalaGen, anthillSmtGen)
  .settings(
    name := "anthill-scaland"
  )

lazy val core = project
  .in(file("core"))
  .settings(
    name := "anthill-core",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
    // WI-1007: a non-exhaustive match is an ERROR, not a warning. `LoadPass.atItem` is
    // the reason — it is the pass whose job is "everything that reaches the KB reaches
    // it here", so an `Item` kind it forgets is data loss, and that is not hypothetical:
    // `constraint` was being parsed and dropped in silence under the `case _` this
    // replaced. A warning would not have carried; the whole point is that ADDING an
    // `Item` kind must stop the build until someone decides what the loader does with it.
    // Costs nothing today: core compiles clean with it (the only standing warnings are
    // four non-local returns, a different id — re-measured under 3.8.4).
    //
    // VERIFIED, and the only way to verify it: nothing in the tree exercises this flag, so
    // a bump that silently retired the E029 id would drop the guard with no test failing.
    // Control run at the 3.6.3 -> 3.8.4 bump — commenting out `atItem`'s `ConstraintItem`
    // arm produced `[E029] Pattern Match Exhaustivity Error`, naming that arm. Re-run it
    // by hand at the next bump; there is nothing else that can.
    scalacOptions += "-Wconf:id=E029:e",
    libraryDependencies ++= Seq(
      "com.lihaoyi" %% "fastparse" % "3.1.1",
      "org.scalameta" %% "munit" % "1.0.0" % Test,
      // WI-1020: the compiler that CHECKS Bootstrap's emitted Scala, invoked in-process
      // through `dotc.Driver`. A resolved dependency rather than a `scala-cli` on PATH:
      // it needs no network at test time, cannot be absent (so there is no skip-when-
      // missing branch to hide a defect behind), and is pinned to `scala3Version` so the
      // harness cannot silently drift from what the build targets.
      "org.scala-lang" %% "scala3-compiler" % scala3Version % Test
    ),
    // WI-1020: the classpath the EMITTED code compiles against, handed to the harness as
    // a resource. Not `System.getProperty("java.class.path")` — sbt runs tests unforked,
    // so that property is the launcher's classpath and carries no scala3-library, and the
    // harness would fail on `Any` rather than on the code under test.
    // `dependencyClasspath` and not `fullClasspath`: emitted code needs the dependencies
    // only, and `fullClasspath` includes this project's `products`, which resources feed —
    // a cycle.
    Test / resourceGenerators += Def.task {
      val out = (Test / resourceManaged).value / "scala-compile-classpath.txt"
      val cp = (Test / dependencyClasspath).value.map(_.data.getAbsolutePath)
      IO.write(out, cp.mkString("\n"))
      Seq(out)
    }.taskValue
  )

// KB-driven anthill → Scala codegen, per proposal 034 §anthill-scala-gen.
// Skeleton today; body lands in a follow-up WI gated on a real consumer.
lazy val anthillScalaGen = project
  .in(file("anthill-scala-gen"))
  .dependsOn(core)
  .settings(
    name := "anthill-scala-gen",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
    libraryDependencies ++= Seq(
      "org.scalameta" %% "munit" % "1.0.0" % Test
    )
  )

// SMT-LIB 2.6 emitter (Z3 / CVC5 target). Mirrors rustland's
// anthill-smt-gen; v0 ports the comm_delay_max round-trip path.
lazy val anthillSmtGen = project
  .in(file("anthill-smt-gen"))
  .dependsOn(core)
  .settings(
    name := "anthill-smt-gen",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
    libraryDependencies ++= Seq(
      "org.scalameta" %% "munit" % "1.0.0" % Test
    )
  )
