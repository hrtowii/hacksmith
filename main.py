from isabelle_client import get_isabelle_client, start_isabelle_server
import json
import logging
import os
from openai import OpenAI
from dotenv import load_dotenv
import argparse
from isabelle_client.isabelle_connector import IsabelleConnector
from isabelle_client.isabelle_connector import IsabelleTheoryError
import time
import re

THEORY_REGEX=r"theory (.*)\n"

def get_theory_name(input_str):
    match = re.search(THEORY_REGEX, input_str)
    if match:
        return match.group(1)
    return None

load_dotenv(".env")

TIMESTAMP = time.time()

class LLM:
    def __init__(self):
        self.client = OpenAI(
            base_url="https://openrouter.ai/api/v1",
            api_key=os.getenv("OPENROUTER_API_KEY"),
        )
        
    def generate(self, prompt):
        response = self.client.chat.completions.create(
            model="google/gemini-3-pro-preview",
            messages=[
                {
                    "role": "user",
                    "content": f"{prompt}"
                }
            ],
            extra_body={"reasoning": {"enabled": True}}
        )
        return response.choices[0].message.content

class Isabelle:
    def __init__(self):
        self.isabelle = self.connect()
        self.connector = IsabelleConnector()

    def connect(self):
        server_info, _ = start_isabelle_server(
            name="test", port=9999, log_file="server.log"
        )
        isabelle = get_isabelle_client(server_info)
        isabelle.logger = logging.getLogger()
        isabelle.logger.setLevel(logging.INFO)
        isabelle.logger.addHandler(logging.FileHandler("session.log"))
        return isabelle

    def prove(self, llm_output):
        ## Take LLM output and pipe it here
        # send a theory file from the current directory to the server
        # self.connector.build_theory(
        #     llm_output, theory=f"generated.{time.time()}"
        # )

        theory_name = get_theory_name(llm_output)

        if theory_name is None:
            theory_name = "Scratch"

            llm_output = f'''
theory {theory_name}
    imports Main
begin

{llm_output}

end
            '''

        with open(f"{theory_name}.thy", "w") as theory_file:
            theory_file.write(llm_output)

        # with open(file, "w") as filething:
        #     file.write(llm_output)
            
        response = self.isabelle.use_theories(
            theories=[theory_name], master_dir=".", watchdog_timeout=0
        )
        self.debug(response)        

    def debug(self, response):
        # Feedback system
        response = response[-1].response_body
        response = json.loads(response)
        nodes = response['nodes'][0]
        messages = nodes['messages']
        print(messages)
        if response['ok']:
            print('Proof succeed!')
            return 0

        print("Failed to finish proof")
        for i in messages:
            print(i['message'])
        return -2


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="take code and formally prove with isabelle using AI test rules"
    )
    parser.add_argument("filename", type=str, help="filename in C")
    parser.add_argument("test", type=str, help="test case in natural language")
    args = parser.parse_args()


    isabelle = Isabelle()
    llm = LLM()
    with open(args.filename) as file:
        content = file.read()


        # llm.generate -> the isabelle vode
        prompt_input = """
Please translate the following code into corresponding isabelle language formal problem. Just translate, do not provide any other text or comments. Always write a proof, even if the software has bugs: if the software is buggy, the intended behavior is that Isabelle will notify that there's an error and the program itself should not do so, so never say sorry or oops.

Example Code:
year = ORIGINYEAR;
while (days > 365) {
    if (IsLeapYear (year)) {
        if (days > 366) {
            days -= days 366;
            year += 1;
        }
    } else {
        days -= 365;
        year += 1;
    }
}

Example Output:
fun zune_step :: "nat ⇒ nat ⇒ (nat × nat)" where
    "zune_step days year =
        (if days > 365 then
            (if isLeapYear year then
                (if days > 366 then (days - 366, year + 1)
                else (days, year))
            else (days - 365, year + 1))
        else (days, year))"

fun zune_loop :: "nat ⇒ nat ⇒ nat ⇒ (nat × nat)" where
"zune_loop fuel days year =
    (if fuel = 0 then (days, year)
    else let (d', y') = zune_step days year
        in if d' = days ∧ y' = year then (d', y')
            else zune_loop (fuel - 1) d' y')"

lemma zune_bug_stuck:
    assumes "isLeapYear year" and "days = 366"
    shows "zune_step days year = (days, year)"
    using assms by simp


""" + f"""
Note that you should only output the body of the Isabelle proof - you do not have to include filename, headers, imports, or codeblock markers. The generated code will go in here:
```isabelle
theory Example.thy
imports Main
begin
<YOUR OUTPUT>
end
```

Write a proof in the Isabelle language. The first step is to convert the given code to fit Isabelle

```
{content}
```

Without using any context of the provided code, next write lemmas that formally prove that {args.test}. 

   Requirements for the lemma(s):
   - Do NOT strengthen the statement to make it true.
   - Do NOT add assumptions to make it provable.
   - If the test case describes a false property, Isabelle must fail. This is correct behavior.
   - Do NOT use "sorry" or "oops".
"""

        theory = llm.generate(prompt_input)
        # theory = theory[11:-3]
        timestamp = time.time()

        with open(f"output_{timestamp}.thy", "w") as file:
            file.write(theory)

        with open(f"prompt_{timestamp}.txt", "w") as file:
            file.write(prompt_input)

        print(theory)
        
        isabelle.prove(theory)