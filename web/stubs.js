// The [stat] and [lstat] of the devices in memory of js_of_ocaml
// (MlFakeDevice), which it does not implement, for [Unix.stat] and
// [Unix.lstat] on their files: a file or a directory, without links.

//Provides: kanon_fake_device_stat
//Requires: MlFakeDevice, ocaml_stats_from_node_stats, caml_raise_no_such_file
function kanon_fake_device_stat(_unit) {
  function stat(name, large, raise_unix) {
    if (!this.exists(name))
      caml_raise_no_such_file(this.nm(name), raise_unix, "stat");
    var dir = this.is_dir(name);
    var size = dir ? 0 : this.content[name].length();
    var now = Date.now();
    return ocaml_stats_from_node_stats(
      {
        isFile: () => !dir,
        isDirectory: () => !!dir,
        dev: 0,
        ino: 0,
        mode: dir ? 0o755 : 0o644,
        nlink: 1,
        uid: 0,
        gid: 0,
        rdev: 0,
        size: size,
        atimeMs: now,
        mtimeMs: now,
        ctimeMs: now,
      },
      large,
    );
  }
  MlFakeDevice.prototype.stat = stat;
  MlFakeDevice.prototype.lstat = stat;
  return 0;
}
