import Alloy.C

open scoped Alloy.C

alloy c include <lean/lean.h> <termios.h> <unistd.h> <sys/ioctl.h> <stdlib.h>

alloy c section
static struct termios orig_termios;
static int raw_mode_enabled = 0;
static int atexit_registered = 0;

#define BNOT(x) ((tcflag_t)(~(x)))

static void restore_terminal(void) {
  if (raw_mode_enabled) {
    tcsetattr(STDIN_FILENO, TCSAFLUSH, &orig_termios);
    raw_mode_enabled = 0;
  }
}
end

alloy c extern "lean_enable_raw_mode"
def enableRawMode : IO Unit :=
  if (!isatty(STDIN_FILENO)) {
    lean_object* err = lean_mk_io_user_error(lean_mk_string("stdin is not a terminal"));
    return lean_io_result_mk_error(err);
  }

  if (raw_mode_enabled) {
    return lean_io_result_mk_ok(lean_box(0));
  }

  if (tcgetattr(STDIN_FILENO, &orig_termios) == -1) {
    lean_object* err = lean_mk_io_user_error(lean_mk_string("tcgetattr failed"));
    return lean_io_result_mk_error(err);
  }

  if (!atexit_registered) {
    atexit(restore_terminal);
    atexit_registered = 1;
  }

  struct termios raw = orig_termios;
  raw.c_iflag &= BNOT(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
  raw.c_oflag &= BNOT(OPOST);
  raw.c_cflag |= (tcflag_t) (CS8);
  raw.c_lflag &= BNOT(ECHO | ICANON | IEXTEN | ISIG);
  raw.c_cc[VMIN] = 0;
  raw.c_cc[VTIME] = 1;

  if (tcsetattr(STDIN_FILENO, TCSAFLUSH, &raw) == -1) {
    lean_object* err = lean_mk_io_user_error(lean_mk_string("tcsetattr failed"));
    return lean_io_result_mk_error(err);
  }

  raw_mode_enabled = 1;
  return lean_io_result_mk_ok(lean_box(0));

alloy c extern "lean_disable_raw_mode"
def disableRawMode : IO Unit :=
  if (!raw_mode_enabled) {
    return lean_io_result_mk_ok(lean_box(0));
  }

  if (tcsetattr(STDIN_FILENO, TCSAFLUSH, &orig_termios) == -1) {
    lean_object* err = lean_mk_io_user_error(lean_mk_string("tcsetattr failed"));
    return lean_io_result_mk_error(err);
  }

  raw_mode_enabled = 0;
  return lean_io_result_mk_ok(lean_box(0));

alloy c extern "lean_is_raw_mode"
def isRawMode : IO Bool :=
  return lean_io_result_mk_ok(lean_box(raw_mode_enabled ? 1 : 0));

alloy c extern "lean_get_terminal_size"
def getTerminalSize : IO (Nat × Nat) :=
  struct winsize ws;
  if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == -1 || ws.ws_col == 0) {
    lean_object* err = lean_mk_io_user_error(lean_mk_string("ioctl failed"));
    return lean_io_result_mk_error(err);
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, lean_usize_to_nat(ws.ws_row));
  lean_ctor_set(pair, 1, lean_usize_to_nat(ws.ws_col));
  return lean_io_result_mk_ok(pair);

alloy c extern "lean_is_tty"
def isTTY : IO Bool :=
  return lean_io_result_mk_ok(lean_box(isatty(STDIN_FILENO) ? 1 : 0));
