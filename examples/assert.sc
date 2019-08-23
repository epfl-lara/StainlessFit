def assert(b: {b: Bool | b}): Unit = { if(b) () else Error[Unit]("Assertion failed") }
