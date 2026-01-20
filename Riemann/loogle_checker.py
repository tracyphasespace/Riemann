import os
import re
import requests
import time
import sys

# CONFIGURATION
# ----------------
SEARCH_PATHS = ["."] 
LOOGLE_API = "https://loogle.lean-lang.org/json"

def clean_signature_for_query(sig):
    # Remove whitespace/newlines to make it a single line
    sig = " ".join(sig.split())
    
    # Heuristic: split by arrow to find the conclusion/result type
    # This helps Loogle focus on *what* is being proved.
    parts = re.split(r'→|->', sig)
    conclusion = parts[-1].strip()
    
    return conclusion

def get_mathlib_matches(query):
    try:
        params = {'q': query}
        print(f"   [API] Querying Loogle: '{query}'...")
        response = requests.get(LOOGLE_API, params=params, timeout=10)
        
        if response.status_code == 200:
            data = response.json()
            if "hits" in data and len(data["hits"]) > 0:
                # Return top 3 hits with their score/name
                return [f"{hit['name']}" for hit in data["hits"][:3]]
    except Exception as e:
        return [f"Error: {e}"]
    return []

def scan_and_check(paths):
    print(f"Scanning project for 'axiom' declarations and checking Loogle...")
    print(f"{'-'*60}")
    
    # Regex captures: axiom <name> <args> : <type>
    # It stops lookahead at the next major keyword to avoid consuming the whole file.
    axiom_pattern = re.compile(
        r'^axiom\s+(?P<name>\w+)\s*(?P<args>[^:]*):\s*(?P<sig>[\s\S]+?)(?=\n(?:axiom|theorem|lemma|def|end|/--|noncomputable|namespace|section|$))',
        re.MULTILINE
    )

    found_count = 0
    
    for path in paths:
        if not os.path.exists(path): continue
        for root, dirs, files in os.walk(path):
            if "lake-packages" in root: continue
            
            for file in files:
                if file.endswith(".lean"):
                    filepath = os.path.join(root, file)
                    with open(filepath, "r", encoding="utf-8") as f:
                        content = f.read()
                        
                    # Remove comments to prevent false positives in commented code
                    content = re.sub(r'/-[\s\S]*?-/', '', content)
                    content = re.sub(r'--.*', '', content)

                    for match in axiom_pattern.finditer(content):
                        name = match.group("name")
                        sig = match.group("sig")
                        
                        found_count += 1
                        print(f"🔍 Axiom: {name}")
                        
                        query = clean_signature_for_query(sig)
                        
                        # If query is very short, it might return too much noise, but we try anyway
                        matches = get_mathlib_matches(query)
                        
                        if matches and not matches[0].startswith("Error"):
                            print(f"   ✅ POTENTIAL MATCHES: {', '.join(matches)}")
                        elif matches:
                            print(f"   ⚠️  API Error: {matches[0]}")
                        else:
                            print(f"   ❌ No exact match found.")
                        print("-" * 20)
                        
                        # Sleep to avoid rate limiting
                        time.sleep(1)
    
    if found_count == 0:
        print("No 'axiom' statements found in the scanned paths.")

if __name__ == "__main__":
    if len(sys.argv) > 1:
        # If arguments are provided, join them as a single query and run it
        custom_query = " ".join(sys.argv[1:])
        print(f"🔎 Custom Query: {custom_query}")
        matches = get_mathlib_matches(custom_query)
        if matches and not matches[0].startswith("Error"):
             print(f"   ✅ MATCHES: {', '.join(matches)}")
        elif matches:
             print(f"   ⚠️  API Error: {matches[0]}")
        else:
             print(f"   ❌ No exact match.")
    else:
        # Default behavior: scan files
        scan_and_check(SEARCH_PATHS)
