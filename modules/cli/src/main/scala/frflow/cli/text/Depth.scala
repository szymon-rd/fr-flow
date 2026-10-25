package frflow.cli
package text

/** `Brief` before a review prompt, `Normal` for `show` (about a screen), `Full` for `show --full` (nothing cut). */
enum Depth:
  case Brief, Normal, Full
