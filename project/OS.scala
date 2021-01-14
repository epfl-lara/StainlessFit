/* Copyright 2019-2020 EPFL, Lausanne */


object OS {
  val osInf = Option(System.getProperty("os.name")).getOrElse("")

  val isUnix    = osInf.indexOf("nix") >= 0 || osInf.indexOf("nux") >= 0
  val isWindows = osInf.indexOf("Win") >= 0
  val isMac     = osInf.indexOf("Mac") >= 0

  val name = if (isWindows) "win" else if (isMac) "mac" else "unix"
  val arch = System.getProperty("sun.arch.data.model")
}
