val scala3Version = "3.6.3"

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
    // four non-local returns, a different id).
    scalacOptions += "-Wconf:id=E029:e",
    libraryDependencies ++= Seq(
      "com.lihaoyi" %% "fastparse" % "3.1.1",
      "org.scalameta" %% "munit" % "1.0.0" % Test
    )
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
