import java.io.File

object Utils {
  def files(dir: String, pred: String => Boolean = _ => true): List[String] = {
    val d = new File(dir)
    d.listFiles.toList.filter((f: File) => f.isFile && pred(f.getPath)).map(_.getPath)
  }
}
