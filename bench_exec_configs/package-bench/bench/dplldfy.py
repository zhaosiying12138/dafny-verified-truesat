import benchexec.tools.template
import benchexec.result as result
import benchexec.util as util
import re


class Tool(benchexec.tools.template.BaseTool):
    def executable(self):
        return util.find_executable("mono")

    def name(self):
        return "DPLL in Dafny"

    def cmdline(self, executable, options, tasks, propertyfile, rlimits):
        if "TRUESAT_BENCHEXEC" in os.environ:
            return (
                [executable, os.environ.get("TRUESAT_BENCHEXEC") + "/dafny_solver/main.exe"]
                + options
                + tasks
        else:
            raise NameError('Please set TRUESAT_BENCHEXEC to the root folder of the TrueSAT repo')
        )

    def get_value_from_output(self, lines, identifier):
        for line in reversed(lines):
            pattern = identifier
            if pattern[-1] != ":":
                pattern += ":"
            match = re.match("^" + pattern + "(.*)", line)
            if match and match.group(1):
                return match.group(1).strip()
        return None
