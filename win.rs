//! Utility functions and helpers specific to Windows

use std::mem::{transmute, size_of, MaybeUninit};
use std::os::raw::{c_int, c_void};
use std::ptr;

use winapi::um::handleapi::INVALID_HANDLE_VALUE;
use winapi::um::processenv::GetStdHandle;
pub use winapi::shared::windef::{HDC, HWND};
pub use winapi::shared::minwindef::DWORD;
use winapi::shared::minwindef::ULONG;
pub use winapi::shared::windef::COLORREF;  // = DWORD
use winapi::um::errhandlingapi::GetLastError;
use winapi::um::winbase::STD_ERROR_HANDLE;
use winapi::um::wincon::{GetConsoleWindow, GetConsoleScreenBufferInfo, GetCurrentConsoleFont};
pub use winapi::um::wincon::CONSOLE_SCREEN_BUFFER_INFO;
pub use winapi::um::wincontypes::CONSOLE_FONT_INFO;
use winapi::um::wingdi::{GetPixel, SetPixelV, StretchDIBits,
  BITMAPINFOHEADER, BITMAPINFO, BI_RGB, CLR_INVALID, DIB_RGB_COLORS, GDI_ERROR, RGB, RGBQUAD, SRCCOPY};
pub use winapi::um::winnt::HANDLE;
use winapi::um::winuser::{GetDC, ReleaseDC};

pub struct DeviceContext {
  /// cf. https://docs.microsoft.com/en-us/windows/console/getconsolewindow
  pub console_window: HWND,
  /// Device Context belonging to `console_window`
  pub dc: HDC,
  /// Hidden Error Handler: for when we can not return (such as in a `drop` RAII)
  pub heh: &'static dyn Fn (&'static str, DWORD),
  /// How wide can we paint, in pixels, set by `scan_size`
  pub width: i32,
  /// How far can we paint, in pixels, set by `scan_size`
  pub height: i32,
  /// Console Error: `STD_ERROR_HANDLE` retrieved with `GetStdHandle`,
  /// need it to get the font size and cursor position from the “console's active screen buffer”,
  /// to align graphics with text
  pub ce: HANDLE}

unsafe impl Send for DeviceContext {}

impl Drop for DeviceContext {
  fn drop (&mut self) {
    let rc = unsafe {ReleaseDC (self.console_window, self.dc)};
    if rc != 1 {(self.heh) ("ReleaseDC(dc)", unsafe {GetLastError()})}}}

impl DeviceContext {
  /// Obtains console window, Device Context and Console Error
  /// * `heh` - Error handler for when we can not return (such as in a `drop` RAII)
  pub fn with_heh (heh: &'static dyn Fn (&'static str, DWORD)) -> Result<DeviceContext, String> {
    let console_window = unsafe {GetConsoleWindow()};
    if console_window == ptr::null_mut() {return ERR! ("!GetConsoleWindow")}

    let dc = unsafe {GetDC (console_window)};
    if dc == ptr::null_mut() {return ERR! ("!GetDC")}

    let ce = unsafe {GetStdHandle (STD_ERROR_HANDLE)};
    if ce == INVALID_HANDLE_VALUE {return ERR! ("!GetStdHandle")}

    Ok (DeviceContext {
      console_window,
      dc,
      heh,
      width: 0,
      height: 0,
      ce})}

  /// Obtains console window, Device Context and Console Error
  pub fn new() -> Result<DeviceContext, String> {
    DeviceContext::with_heh (&|_label, _errno| {})}

  /// Packs RGB for a `stretch_to` pixel
  pub fn rgba (r: u8, g: u8, b: u8) -> u32 {
    let quad = RGBQUAD {
      rgbBlue: b,
      rgbGreen: g,
      rgbRed: r,
      rgbReserved: 0};
    unsafe {transmute (quad)}}

  /// Paints the given `rgba`  
  /// Stretches the image if `w` <> `sw` or `h` <> `sh`  
  /// `rgba` position `i = iy * sw + ix`
  pub fn stretch (&self, x: i32, y: i32, w: i32, h: i32, sx: i32, sy: i32, sw: i32, sh: i32, rgba: &[u32])
  -> Result<i32, DWORD> {
    let mut inf: BITMAPINFO = unsafe {MaybeUninit::zeroed().assume_init()};
    inf.bmiHeader.biSize = size_of::<BITMAPINFOHEADER>() as u32;
    inf.bmiHeader.biWidth = sw;
    inf.bmiHeader.biHeight = -sh;  // “top-down DIB”
    inf.bmiHeader.biPlanes = 1;
    inf.bmiHeader.biBitCount = 32;
    inf.bmiHeader.biCompression = BI_RGB;
    inf.bmiHeader.biSizeImage = (sw * sh * 4) as u32;

    // https://docs.microsoft.com/en-us/windows/win32/api/wingdi/nf-wingdi-stretchdibits
    let rc = unsafe {StretchDIBits (
      self.dc, x, y, w, h, sx, sy, sw, sh, rgba.as_ptr() as *const c_void, &inf, DIB_RGB_COLORS, SRCCOPY)};
    if rc == 0 || rc as ULONG == GDI_ERROR {Err (unsafe {GetLastError()})} else {Ok (rc)}}

  /// cf. https://docs.microsoft.com/en-us/windows/win32/api/wingdi/nf-wingdi-setpixelv
  pub fn set_pixel (&self, x: i32, y: i32, r: u8, g: u8, b: u8) -> Result<(), DWORD> {
    let rc = unsafe {SetPixelV (self.dc, x, y, RGB (r, g, b))};
    if rc == 0 {Err (unsafe {GetLastError()})} else {Ok(())}}

  /// cf. https://docs.microsoft.com/en-us/windows/win32/gdi/colorref  
  /// NB: Looks like the window needs to be visible in order for `get_pixel` to work
  pub fn get_pixel (&self, x: i32, y: i32) -> Result<COLORREF, ()> {
    let rc = unsafe {GetPixel (self.dc, x as c_int, y as c_int)};
    if rc == CLR_INVALID {
      Err (())
    } else {
      Ok (rc)}}

  /// Experimentally determine max `width` and `height` in pixels  
  /// NB: Looks like the window needs to be visible in order for `get_pixel` to work
  pub fn scan_size (&mut self) {
    if let Err (()) = self.get_pixel (1, 1) {  // Return early if `get_pixel` doesn't work (window hidden)
      let errno = unsafe {GetLastError()};
      if errno != 0 {(self.heh) ("get_pixel (1, 1)", errno)}
      return}

    // NB: GetDeviceCaps with HORZRES and VERTRES returns bogus values
    //   GetWindowRect too: it seems to match results obtained
    //   multiplying GetConsoleFontSize by GetConsoleScreenBufferInfo/dwSize,
    //   but the actual number of pixels is different
    let (mut width, mut height) = (0, 0);
    while self.get_pixel (width + 31, height + 31) .is_ok() {width += 31; height += 31}
    while self.get_pixel (width + 9, height) .is_ok() {width += 9}
    while self.get_pixel (width + 1, height) .is_ok() {width += 1}
    while self.get_pixel (width, height + 1) .is_ok() {height += 1}
    self.width = width + 1; self.height = height + 1}

  /// cf. https://docs.microsoft.com/en-us/windows/console/console-font-info-str
  pub fn font (&self) -> Result<CONSOLE_FONT_INFO, String> {
    let mut font: CONSOLE_FONT_INFO = unsafe {MaybeUninit::zeroed().assume_init()};
    let rc = unsafe {GetCurrentConsoleFont (self.ce, 0, &mut font)};
    if rc == 0 {ERR! ("!GetCurrentConsoleFont")} else {Ok (font)}}

  /// cf. https://docs.microsoft.com/en-us/windows/console/console-screen-buffer-info-str
  pub fn screen_buffer_info (&self) -> Result<CONSOLE_SCREEN_BUFFER_INFO, DWORD> {
    let mut sbi: CONSOLE_SCREEN_BUFFER_INFO = unsafe {MaybeUninit::zeroed().assume_init()};
    let rc = unsafe {GetConsoleScreenBufferInfo (self.ce, &mut sbi)};
    if rc == 0 {Err (unsafe {GetLastError()})} else {Ok (sbi)}}

  /// Bridges character position to pixels  
  /// Depends on `scan_size` (called separately) to know the actual pixel dimensions
  pub fn translate (&self) -> Result<(Translation, CONSOLE_SCREEN_BUFFER_INFO), String> {
    let sbi = try_s! (self.screen_buffer_info());
    // The actual character size in Windows might differ from the one reported in `CONSOLE_FONT_INFO`
    let (mut tw, mut th) = (1, 2);
    let sw = (sbi.srWindow.Right - sbi.srWindow.Left) as i16;
    if sw > 0 {while (tw + 1) as i32 * sw as i32 <= self.width {tw += 1}}

    let sh = (sbi.srWindow.Bottom - sbi.srWindow.Top) as i16 + 1;
    if sh > 0 {while (th + 1) as i32 * sh as i32 <= self.height {th += 1}}
    //println! ("\nself.height {} vs th*sh= {}; th {}\n", self.height, th as i16 * sh, th);

    Ok ((Translation {
      cxa: sbi.dwCursorPosition.X as i16,
      left: sbi.srWindow.Left as i16,
      cya: sbi.dwCursorPosition.Y as i16,
      top: sbi.srWindow.Top as i16,
      sw,
      sh,
      tw,
      th
    }, sbi))}}

/// Bridges character position to pixels
#[derive(Clone, Debug)]
pub struct Translation {
  /// Cursor X, Absolute, in characters, 0-based
  pub cxa: i16,
  /// Horizontal scrolling
  pub left: i16,
  /// Cursor Y, Absolute, in characters, 0-based  
  /// Mind the scrolling: if `cy` equals `sh` then the measurement
  /// was taken at the bottom of the visible screen  
  /// Also with lines recently printed on
  /// the actual *paint* of characters by the terminal might happen after a small delay,
  /// overwriting whatever graphics we put there: should either wait for the terminal *paint* to settle
  /// or better yet maintain a set of overlays to be redrawn periodically
  pub cya: i16,
  /// Vertical scrolling
  pub top: i16,
  /// Screen Width in characters (`Right - Left`)
  pub sw: i16,
  /// Screen Height in characters (`Bottom - Top`)
  pub sh: i16,
  /// Text Width: a likely number of horisontal pixels in a character
  pub tw: i8,
  /// Text Height: a likely number of vertical pixels in a character
  pub th: i8}

impl Translation {
  pub fn cx (&self) -> i32 {
    self.cxa as i32 - self.left as i32}

  pub fn cy (&self) -> i32 {
    self.cya as i32 - self.top as i32}}
