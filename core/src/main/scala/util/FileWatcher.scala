/* Copyright 2009-2018 EPFL, Lausanne */

package util

import java.io.{ File, PrintWriter }
import java.nio.file.{ FileSystems, Path, StandardWatchEventKinds }
import java.util.concurrent.TimeUnit

import scala.collection.JavaConverters._
import scala.collection.mutable.{ Map => MutableMap }

/**
 * Facility to run an [[action]] whenever any of the given [[files]] are updated.
 *
 * The [[files]] should refer to absolute paths.
 *
 * Code taken from: https://github.com/epfl-lara/stainless/blob/0b10d1725319f4d2295f2b0bbfb59f6739191e99/core/src/main/scala/stainless/utils/FileWatcher.scala
 */
class FileWatcher(files: Set[File], action: () => Unit) {

  def run(): Unit = {
    action()

    // Watch each individual file for modification through their parent directories
    // (because a WatchService cannot observe files directly..., also we need to keep
    // track of the modification time because we sometimes receive several events
    // for the same file...)
    val watcher = FileSystems.getDefault.newWatchService()
    val times = MutableMap[File, Long]() ++ (files map { f => f -> f.lastModified })
    val dirs: Set[Path] = files map { _.getParentFile.toPath }
    dirs foreach { _.register(watcher, StandardWatchEventKinds.ENTRY_MODIFY) }

    println(s"\n\nWaiting for source changes...\n\n")

    while (true) {
      // Wait for further changes, filtering out everything that is not of interest

      val key = watcher.poll(500, TimeUnit.MILLISECONDS)
      if (key != null) {
        val events = key.pollEvents()
        val relativeDir = key.watchable.asInstanceOf[Path]
        val notifications = events.asScala map { _.context } collect {
          case p: Path => relativeDir.resolve(p).toFile
        }
        val modified = notifications filter files

        // Update the timestamps while looking for things to process.
        // Note that timestamps are not 100% perfect filters: the files could have the same content.
        // But it's very lightweight and the rest of the pipeline should be able to handle similar
        // content anyway.
        var proceed = false
        for {
          f <- modified
          if f.lastModified > times(f)
        } {
          proceed = true
          times(f) = f.lastModified
        }

        if (proceed) {
          println(s"Detecting some file modifications...: ${modified mkString ", "}")
          action()
          println(s"\n\nWaiting for source changes...\n\n")
        }

        val valid = key.reset()
        if (!valid) println(s"Watcher is no longer valid for $relativeDir!")
      }
    }

    watcher.close()
  }

}
