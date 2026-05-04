val scala3Version = "3.6.3"

lazy val root = project
  .in(file("."))
  .aggregate(core, anthillScalaGen)
  .settings(
    name := "anthill-scaland"
  )

lazy val core = project
  .in(file("core"))
  .settings(
    name := "anthill-core",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
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
