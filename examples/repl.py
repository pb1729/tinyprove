# Tinyprove REPL
# Warning: Experimental

# Reading: The parser reads in source code on demand from user input. It will not know that you have finished a definition until you've typed the trailing comma.
# Printing: For each definition, we print out the values that it caused to be defined (not including submodules). This can sometimes result in the quote function generating large expressions.


from tinyprove import get_usual_axioms, def_module, get_value_for_const, quote, EmptyEnv
from tinyprove.ir import LineInfo
from tinyprove.parser import Parser, _tokenise


def line_info_rollback(line_info:LineInfo, pos:int):
  """ MUTATES line_info to reset it to token number pos """
  line_info.line_nums = line_info.line_nums[:pos]
  line_info.lines = line_info.lines[:max(line_info.line_nums, default=1) - line_info.initial_num]
  line_info.tok_start_offsets = line_info.tok_start_offsets[:pos]

def line_info_extend(line_info:LineInfo, new_line_info:LineInfo, pos:int):
  """ MUTATES line_info to add info for new tokens """
  assert line_info.initial_num + len(line_info.lines) == new_line_info.initial_num
  line_info.line_nums.extend(new_line_info.line_nums)
  line_info.lines.extend(new_line_info.lines)
  line_info.tok_start_offsets.extend(new_line_info.tok_start_offsets)


class ReplParser(Parser):
  """ overrides some methods of the usual tinyprove parser in order to
      continually parse and yield definitions from user-provided input """
  def _rollback(self, pos):
    self.pos = pos
    self.toks = self.toks[:pos]
    line_info_rollback(self.line_info, pos)
    self.indty_name = None
    self.env = EmptyEnv()
  def _query_more_tokens(self):
    src = input("> ")
    curr_line_num = self.line_info.initial_num + len(self.line_info.lines)
    new_tokens, new_line_info = _tokenise(src, initial_line_num=curr_line_num)
    self.toks.extend(new_tokens)
    line_info_extend(self.line_info, new_line_info, self.pos)
  def _peek(self):
    while self.pos >= len(self.toks):
      self._query_more_tokens()
    return self.toks[self.pos]
  def defns_generator(self):
    while True:
      defn_start = self.pos
      try:
        defn = self._parse_defn()
        self._eat(",")
      except SyntaxError as e:
        print(e)
        self._rollback(defn_start)
      else:
        yield defn


def remove_new(existing:set, current:dict):
  to_remove = [
    nm
    for nm in current
    if nm not in existing
  ]
  for nm in to_remove:
    del current[nm]

def apply_def(module, defn):
  existing_entries = set(nm for nm in module.entries)
  existing_submodules = set(nm for nm in module.submodules)
  try:
    defn.apply(module)
  except Exception as e:
    print(e)
    if e.__cause__ is not None:
      print(e.__cause__)
    # revert any partially added changes
    remove_new(existing_entries, module.entries)
    remove_new(existing_submodules, module.submodules)
  else: # if we were successful, print out any newly added values
    for nm in module.entries:
      if nm not in existing_entries:
        print(nm, "=", quote(get_value_for_const(module, nm)).str(EmptyEnv()))


base = get_usual_axioms()
mod = def_module("", imports=[("", base)])

repl_parser = ReplParser([], LineInfo(1, [], [], []))
for defn in repl_parser.defns_generator():
  apply_def(mod, defn)



