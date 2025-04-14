import json
import re
    
    

def clean_set_option(text):
    if 'set_option' in text:
        return ''
    else:
        return text
        

def remove_comment(text):
    idx = text.find('--')
    if idx >= 0:
        return text[:idx]
    else:
        return text

def extract_proofs(filename, clean_comment_text=False):
    with open(filename, 'r') as f:
        txt = f.read()
    blocks = re.split(r'(?=^(?:lemma|theorem)\b)', txt, flags = re.MULTILINE)
    
    header = blocks[0]
    header = '\n'.join([clean_set_option(l) for l in header.split('\n')])
    
    # print(header)
    
    lst = []
    
    for block in blocks[1:]:
        # print(block)
        match = re.match(r'^(?:lemma|theorem)\s+(\S+)', block.strip())
        name = match.group(1) if match else None
        # print(name)
        block = re.sub(r'\n+', '\n', block)
        
        # block = '\n'.join([remove_comment(l) for l in block.split('\n')])
        if clean_comment_text:
            block = '\n'.join([remove_comment(l) for l in block.split('\n') if remove_comment(l).strip() != ''])
        
        marker = ':= by'
        idx = block.find(marker)
        
        formal_statement = block[:idx+len(marker)]
        formal_proof = block[idx+len(marker):]
        if 'imo_' not in name:
            print(name)
        
        t = {
            'name' : name,
            'split' : 'train',
            'header' : header,
            'informal_prefix' : '',
            'formal_statement' : formal_statement,
            'formal_proof' : formal_proof,
            }
        lst.append(t)
    return lst
        

def lean_to_jsonl(leanfile, clean_comment_text=False, save_path = './test'):
    theorems = extract_proofs(leanfile, clean_comment_text=clean_comment_text)
    
    with open(save_path, 'w') as f:
        for item in theorems:
            f.write(json.dumps(item, ensure_ascii=False) + '\n')
            

            
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            

    
        