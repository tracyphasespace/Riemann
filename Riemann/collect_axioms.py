import os
import re

# CONFIGURATION
# ----------------
PROJECT_ROOTS = ["./GlobalBound", "./ProofEngine", "./ZetaSurface"] 
MASTER_FILE = "Master_Pending_Axioms.lean"

def promote_sorry_to_axiom(content):
    """
    Refactors 'theorem X : T := sorry' to 'axiom X : T'
    Returns: (new_content, list_of_converted_names)
    """
    # Regex to find theorems ending in sorry. 
    # Captures: (Type)(Name)(Args)(Type)(:= sorry)
    # Note: simple heuristic; complex multi-line definitions might need manual review.
    pattern = re.compile(
        r'(?P<indent>\s*)(?:theorem|lemma)\s+(?P<name>\w+)\s*(?P<args>[^:]*):\s*(?P<type>[\s\S]+?)(?::=|by)[\s\S]*?\bsorry\b',
        re.MULTILINE
    )

    converted = []
    
    def replacer(match):
        indent = match.group("indent")
        name = match.group("name")
        args = match.group("args")
        type_sig = match.group("type")
        
        converted.append(name)
        # Convert to axiom syntax (no := sorry)
        return f"{indent}axiom {name} {args}:{type_sig}"

    new_content = pattern.sub(replacer, content)
    return new_content, converted

def scan_and_promote(roots):
    all_axioms = []
    
    print("🚀 Starting Axiom Promotion & Collection...")
    
    for root_dir in roots:
        if not os.path.exists(root_dir): continue
        
        for dirpath, _, filenames in os.walk(root_dir):
            for filename in filenames:
                if filename.endswith(".lean"):
                    filepath = os.path.join(dirpath, filename)
                    
                    with open(filepath, "r", encoding="utf-8") as f:
                        content = f.read()
                    
                    # 1. Promote in-place
                    new_content, converted_names = promote_sorry_to_axiom(content)
                    
                    if converted_names:
                        print(f"  Refactored {len(converted_names)} theorems in {filename}")
                        # Overwrite file with new 'axiom' keywords
                        with open(filepath, "w", encoding="utf-8") as f:
                            f.write(new_content)
                            
                        # 2. Collect for the Master List
                        # We grab the *signature* to put in the cheat sheet
                        # (We just use the names for the summary to save tokens)
                        for name in converted_names:
                            all_axioms.append(f"axiom {name} -- Source: {filename}")

    # Write the Master Index
    with open(MASTER_FILE, "w", encoding="utf-8") as f:
        f.write("/-- MASTER AXIOM COLLECTOR --/\n")
        f.write("/-- This file lists all pending proofs refactored as axioms. --/\n")
        f.write("/-- Feed this list to the AI to prioritize work. --/\n\n")
        f.write("\n".join(all_axioms))
        
    print(f"\n✅ Done! {len(all_axioms)} 'sorrys' promoted to 'axioms'.")
    print(f"📜 Summary saved to: {MASTER_FILE}")

if __name__ == "__main__":
    scan_and_promote(PROJECT_ROOTS)
