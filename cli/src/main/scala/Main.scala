object Main {
  def main(args: Array[String]): Unit = {
    Config.parse(args).foreach(App.launch)
  }
}
