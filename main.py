import tkinter as tk
from tkinter import ttk, messagebox
import json
import os
import sys
import time
import subprocess
import threading
from datetime import datetime
import urllib.request
import urllib.error
import re

try:
    from PIL import Image, ImageTk
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False

def get_base_directory():
    if getattr(sys, 'frozen', False):
        return os.path.dirname(sys.executable)
    else:
        return os.path.dirname(os.path.abspath(__file__))

class Ducanator:
    def __init__(self, root):
        self.root = root
        self.root.title("Ducanator")
        self.root.geometry("800x1000")
        self.root.configure(bg="#0f0f0f")
        self.root.attributes('-topmost', True)
        
        self.marked_items_file = "marked_items.json"
        self.marked_items = self.load_marked_items()
        self.platinum_filter_marked = set()
        
        self.data_source = "Not loaded"
        self.inventory_data = []
        self.primary_items = []
        self.inventory_dict = {}
        self.item_category_map = {}
        
        self.search_text = ""
        self.ducat_filter = ""
        self.platinum_filter = ""
        self.platinum_sort_state = 0
        self.amount_sort_state = 0
        self.show_marked = True
        self.selected_category = "ALL"
        
        base_dir = get_base_directory()
        self.cached_data_dir = os.path.join(base_dir, "cachedData")
        
        self.ducat_icon_small = None
        
        self.price_cache = {}
        self.price_cache_file = os.path.join(self.cached_data_dir, "price_cache.json")
        self.load_price_cache()
        self.price_fetch_in_progress = False
        
        self.category_files = {
            "ALL": None,
            "Warframes": [os.path.join(self.cached_data_dir, "Warframes.json")],
            "Primary": [os.path.join(self.cached_data_dir, "Primary.json")],
            "Secondary": [os.path.join(self.cached_data_dir, "Secondary.json")],
            "Melee": [os.path.join(self.cached_data_dir, "Melee.json")],
            "Companions": [
                os.path.join(self.cached_data_dir, "Sentinels.json"),
                os.path.join(self.cached_data_dir, "SentinelWeapons.json")
            ],
            "Archwing": [
                os.path.join(self.cached_data_dir, "Arch-Gun.json"),
                os.path.join(self.cached_data_dir, "Arch-Melee.json"),
                os.path.join(self.cached_data_dir, "Archwing.json")
            ]
        }
        
        self.setup_ui()
        self.load_inventory_from_json()
        self.refresh_display()
    
    def load_marked_items(self):
        if os.path.exists(self.marked_items_file):
            try:
                with open(self.marked_items_file, 'r') as f:
                    return set(json.load(f))
            except:
                return set()
        return set()
    
    def save_marked_items(self):
        with open(self.marked_items_file, 'w') as f:
            json.dump(list(self.marked_items), f)
    
    def load_price_cache(self):
        if os.path.exists(self.price_cache_file):
            try:
                with open(self.price_cache_file, 'r', encoding='utf-8') as f:
                    self.price_cache = json.load(f)
            except:
                self.price_cache = {}
        else:
            self.price_cache = {}
    
    def save_price_cache(self):
        try:
            with open(self.price_cache_file, 'w', encoding='utf-8') as f:
                json.dump(self.price_cache, f, indent=2)
        except:
            pass
    
    def item_name_to_slug(self, item_name):
        slug = item_name.lower().strip()
        slug = slug.replace('&', 'and')
        slug = re.sub(r'\s+', '_', slug)
        slug = re.sub(r'[^a-z0-9_]', '', slug)
        
        if 'kompressa' in slug and 'receiver' in slug:
            slug = slug.replace('receiver', 'reciever')
        
        return slug
    
    def get_warframe_slug_variations(self, item_name):
        component_types = ['neuroptics', 'chassis', 'systems']
        item_lower = item_name.lower()
        base_slug = self.item_name_to_slug(item_name)
        variations = [base_slug]
        
        if 'prime' in item_lower:
            for component in component_types:
                if component in item_lower:
                    slug_parts = base_slug.split('_')
                    if 'prime' in slug_parts:
                        prime_idx = slug_parts.index('prime')
                        if prime_idx > 0:
                            warframe_name = slug_parts[prime_idx - 1]
                            variation_with_blueprint = f"{warframe_name}_prime_{component}_blueprint"
                            if variation_with_blueprint not in variations:
                                variations.append(variation_with_blueprint)
                    break
        
        return variations
    
    def _calculate_reasonable_price(self, prices):
        if not prices:
            return None
        
        sorted_prices = sorted(prices)
        filtered_prices = sorted_prices.copy()
        
        changed = True
        while changed and len(filtered_prices) > 1:
            changed = False
            for i in range(len(filtered_prices) - 1):
                if filtered_prices[i] < (filtered_prices[i + 1] / 2.0):
                    filtered_prices.pop(i)
                    changed = True
                    break
        
        if len(filtered_prices) < max(1, len(sorted_prices) * 0.25):
            filtered_prices = sorted_prices
        
        n = len(filtered_prices)
        if n == 0:
            return None
        
        if n % 2 == 0:
            median = (filtered_prices[n // 2 - 1] + filtered_prices[n // 2]) / 2.0
        else:
            median = filtered_prices[n // 2]
        
        best_price = None
        min_distance = float('inf')
        for price in filtered_prices:
            distance = abs(price - median)
            if distance < min_distance or (distance == min_distance and price < best_price):
                min_distance = distance
                best_price = price
        
        return int(best_price) if best_price is not None else int(filtered_prices[0])
    
    def _try_fetch_price_with_slug(self, slug):
        api_url = f"https://api.warframe.market/v2/orders/item/{slug}"
        
        try:
            req = urllib.request.Request(
                api_url,
                headers={
                    'User-Agent': 'Ducanator/1.0',
                    'Accept': 'application/json'
                }
            )
            
            with urllib.request.urlopen(req, timeout=5) as response:
                data = json.loads(response.read().decode('utf-8'))
                
                if data.get('error'):
                    return None
                
                orders = data.get('data', [])
                if isinstance(orders, dict):
                    orders = orders.get('payload', {}).get('orders', [])
                
                if not isinstance(orders, list) or not orders:
                    return None
                
                sell_orders = [
                    order for order in orders
                    if order.get('type') == 'sell' and order.get('visible', True)
                ]
                
                if not sell_orders:
                    return None
                
                prices = [order.get('platinum', 0) for order in sell_orders if order.get('platinum', 0) > 0]
                if not prices:
                    return None
                
                return self._calculate_reasonable_price(prices)
                
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return None
            return None
        except Exception as e:
            return None
    
    def fetch_market_price(self, item_name, force_refresh=False):
        if not force_refresh:
            if item_name in self.price_cache:
                cached_price = self.price_cache[item_name]
                if isinstance(cached_price, dict) and 'price' in cached_price:
                    if time.time() - cached_price.get('timestamp', 0) < 3600:
                        return cached_price['price']
        
        slug = self.item_name_to_slug(item_name)
        if not slug:
            return None
        
        price = self._try_fetch_price_with_slug(slug)
        if price is not None:
            self.price_cache[item_name] = {
                'price': price,
                'timestamp': time.time()
            }
            self.save_price_cache()
            return price
        
        variations = self.get_warframe_slug_variations(item_name)
        for variation in variations[1:]:
            price = self._try_fetch_price_with_slug(variation)
            if price is not None:
                self.price_cache[item_name] = {
                    'price': price,
                    'timestamp': time.time()
                }
                self.save_price_cache()
                return price
        
        self.price_cache[item_name] = {
            'price': None,
            'timestamp': time.time()
        }
        return None
    
    def fetch_prices_for_items(self, items, force_refresh=False):
        if self.price_fetch_in_progress:
            return
        
        def fetch_in_thread():
            self.price_fetch_in_progress = True
            try:
                items_to_fetch = []
                for item in items:
                    item_name = item.get('name', '')
                    if not item_name or item_name.startswith('---'):
                        continue
                    
                    if not force_refresh:
                        if item_name in self.price_cache:
                            cached = self.price_cache[item_name]
                            if isinstance(cached, dict) and 'price' in cached:
                                if time.time() - cached.get('timestamp', 0) < 3600:
                                    continue
                    
                    items_to_fetch.append(item_name)
                
                if not items_to_fetch:
                    self.root.after(0, self._update_status_with_file_time)
                    return
                
                total = len(items_to_fetch)
                request_count = 0
                start_time = time.time()
                fetched_count = 0
                
                self.root.after(0, lambda: self.status_label.config(text=f"Fetching {total} prices..."))
                
                for idx, item_name in enumerate(items_to_fetch):
                    current_time = time.time()
                    elapsed = current_time - start_time
                    
                    if request_count >= 3 and elapsed < 1.0:
                        wait_time = 1.0 - elapsed
                        if wait_time > 0:
                            time.sleep(wait_time)
                        request_count = 0
                        start_time = time.time()
                    
                    price = self.fetch_market_price(item_name, force_refresh=force_refresh)
                    request_count += 1
                    if price is not None:
                        fetched_count += 1
                    
                    if (idx + 1) % 20 == 0:
                        self.root.after(0, lambda c=fetched_count, t=idx+1, tot=total: 
                                      self.status_label.config(text=f"Fetching prices... {c}/{tot}"))
                    
                    if (idx + 1) % 25 == 0 or idx == total - 1:
                        self.root.after(0, self.refresh_display)
                    
                    time.sleep(1.0 / 3.0)
                
                self.save_price_cache()
                if fetched_count > 0:
                    self.root.after(0, lambda: self.status_label.config(text=f"Fetched {fetched_count} prices"))
                self.root.after(0, self.refresh_display)
                self.root.after(2000, self._update_status_with_file_time)
            finally:
                self.price_fetch_in_progress = False
        
        thread = threading.Thread(target=fetch_in_thread, daemon=True)
        thread.start()
    
    def manual_fetch_all_prices(self):
        if not self.inventory_data:
            messagebox.showinfo("No Data", "No inventory data loaded. Please load inventory first.")
            return
        
        result = messagebox.askyesno(
            "Fetch All Prices",
            f"This will fetch prices for {len(self.inventory_data)} items.\n\n"
            "This may take a while due to rate limiting (3 requests/second).\n\n"
            "Continue?"
        )
        
        if result:
            self.fetch_prices_for_items(self.inventory_data, force_refresh=True)
    
    def run_api_helper_threaded(self, callback):
        base_dir = get_base_directory()
        cached_data_dir = os.path.join(base_dir, "cachedData")
        exe_path = os.path.join(cached_data_dir, "warframe-api-helper.exe")
        
        if not os.path.exists(exe_path):
            messagebox.showerror("Error", f"warframe-api-helper.exe not found!\n\nLooking for: {os.path.abspath(exe_path)}\n\nPlease make sure the executable is in the cachedData folder.")
            callback(False)
            return
        
        self.status_label.config(text="Running API helper...")
        self.root.update()
        self.root.after(7000, lambda: self._auto_refresh_after_reload())
        
        def run_in_thread():
            try:
                abs_exe_path = os.path.abspath(exe_path)
                process = subprocess.Popen(
                    [abs_exe_path],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    cwd=cached_data_dir,
                    creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0
                )
                
                stdout, stderr = process.communicate()
                
                if process.returncode != 0:
                    error_msg = stderr.decode('utf-8', errors='ignore') if stderr else "Unknown error"
                    stdout_msg = stdout.decode('utf-8', errors='ignore') if stdout else ""
                    full_error = f"{error_msg}\n\nSTDOUT:\n{stdout_msg}" if stdout_msg else error_msg
                    self.root.after(0, lambda: messagebox.showerror("Error", f"Failed to run warframe-api-helper.exe:\n\n{full_error}"))
                
            except Exception as e:
                import traceback
                error_trace = traceback.format_exc()
                self.root.after(0, lambda: messagebox.showerror("Error", f"Failed to run warframe-api-helper.exe:\n\n{str(e)}\n\n{error_trace}"))
        
        thread = threading.Thread(target=run_in_thread, daemon=True)
        thread.start()
    
    def _auto_refresh_after_reload(self):
        self.status_label.config(text="Refreshing inventory...")
        self.root.update()
        self._load_inventory_data_threaded()
    
    def _update_status_with_file_time(self):
        inventory_path = os.path.join(self.cached_data_dir, "inventory.json")
        
        if os.path.exists(inventory_path):
            try:
                mtime = os.path.getmtime(inventory_path)
                dt = datetime.fromtimestamp(mtime)
                time_str = dt.strftime("%I:%M:%S %p")
                date_str = dt.strftime("%d.%m.%Y")
                status_text = f"Data Loaded: {time_str}\n{date_str}"
                self.status_label.config(text=status_text)
            except Exception as e:
                self.status_label.config(text="Ready")
        else:
            self.status_label.config(text="Ready")
    
    def load_inventory_from_json(self, run_api_helper_first=False):
        if run_api_helper_first:
            self.run_api_helper_threaded(self._on_api_helper_complete)
            return
        self._load_inventory_data_threaded()
    
    def _on_api_helper_complete(self, success):
        if success:
            self._load_inventory_data_threaded()
        else:
            self.data_source = "API helper failed"
            self.status_label.config(text="API helper failed")
    
    def _load_inventory_data_threaded(self):
        def load_in_thread():
            try:
                self.root.after(0, lambda: self.status_label.config(text="Loading inventory..."))
                
                inventory_path = os.path.join(self.cached_data_dir, "inventory.json")
                if not os.path.exists(inventory_path):
                    self.root.after(0, lambda: messagebox.showerror("Error", "inventory.json not found!\n\nClick 'Reload JSON' to generate it from the API helper."))
                    self.root.after(0, lambda: setattr(self, 'data_source', "inventory.json not found"))
                    return
                
                with open(inventory_path, 'r', encoding='utf-8') as f:
                    inventory_data = json.load(f)
                
                self.inventory_dict = {}
                self._flatten_inventory(inventory_data)
                
                all_prime_items = []
                loaded_files = []
                item_category_map = {}
                
                for category, file_list in self.category_files.items():
                    if category == "ALL":
                        continue
                    if not file_list:
                        continue
                    if not isinstance(file_list, list):
                        file_list = [file_list]
                    
                    for filename in file_list:
                        if filename and os.path.exists(filename):
                            try:
                                with open(filename, 'r', encoding='utf-8') as f:
                                    category_data = json.load(f)
                                
                                prime_items = [item for item in category_data if item.get('isPrime', False)]
                                
                                for item in prime_items:
                                    unique_name = item.get('uniqueName', '')
                                    if unique_name:
                                        item_category_map[unique_name] = category
                                
                                all_prime_items.extend(prime_items)
                                loaded_files.append(filename)
                            except Exception as e:
                                print(f"Error loading {filename}: {e}")
                
                primary_fallback = os.path.join(self.cached_data_dir, "Primary.json")
                if not loaded_files and os.path.exists(primary_fallback):
                    with open(primary_fallback, 'r', encoding='utf-8') as f:
                        primary_data = json.load(f)
                    prime_items = [item for item in primary_data if item.get('isPrime', False)]
                    all_prime_items.extend(prime_items)
                    loaded_files.append(primary_fallback)
                
                if not loaded_files:
                    self.root.after(0, lambda: messagebox.showerror("Error", "No category JSON files found!\n\nExpected files:\n- Primary.json\n- Secondary.json\n- Melee.json\n- Warframes.json\n- Companions.json\n- Archwing.json"))
                    self.root.after(0, lambda: setattr(self, 'data_source', "No JSON files found"))
                    return
                
                self.primary_items = all_prime_items
                self.item_category_map = item_category_map
                self.inventory_data = self.extract_prime_items(all_prime_items)
                self.data_source = f"JSON Files ({len(self.inventory_data)} items from {len(loaded_files)} files)"
                
                self.root.after(0, self.refresh_display)
                if self.inventory_data:
                    self.root.after(1000, lambda: self.fetch_prices_for_items(self.inventory_data))
                
            except Exception as e:
                self.root.after(0, lambda: messagebox.showerror("Error", f"Failed to load JSON files:\n{e}"))
                self.root.after(0, lambda: setattr(self, 'data_source', f"Error: {str(e)}"))
        
        thread = threading.Thread(target=load_in_thread, daemon=True)
        thread.start()
    
    def _flatten_inventory(self, data, prefix=""):
        if isinstance(data, dict):
            for key, value in data.items():
                if key == "ItemType" and isinstance(value, str):
                    item_count = data.get("ItemCount", 0)
                    if item_count > 0:
                        self.inventory_dict[value] = item_count
                elif isinstance(value, (dict, list)):
                    self._flatten_inventory(value, f"{prefix}.{key}")
        elif isinstance(data, list):
            for item in data:
                if isinstance(item, (dict, list)):
                    self._flatten_inventory(item, prefix)
    
    def extract_prime_items(self, items_list=None):
        if items_list is None:
            items_list = self.primary_items
        
        inventory_items = []
        
        valid_component_types = {
            'Blueprint', 'Barrel', 'Receiver', 'Stock', 'Link', 
            'Blade', 'Hilt', 'Handle', 'Grip', 'Lower Limb', 'Upper Limb',
            'String', 'Chassis', 'Neuroptics', 'Systems', 'Harness',
            'Cerebrum', 'Carapace', 'Wings', 'Head', 'Gauntlet',
            'Boot', 'Blades', 'Disc', 'Ornament', 'Stars', 'Chain',
            'Pouch', 'Band', 'Buckle', 'Prime Blueprint'
        }
        
        resource_keywords = [
            'Orokin Cell', 'Neurodes', 'Argon Crystal', 'Cryotic', 'Ferrite',
            'Alloy Plate', 'Rubedo', 'Plastids', 'Nano Spores', 'Polymer Bundle',
            'Circuits', 'Salvage', 'Nano Spores', 'Control Module', 'Morphics',
            'Gallium', 'Neural Sensors', 'Oxium', 'Tellurium', 'Hexenon',
            'Thrax Plasm', 'Entrati Lanthorn', 'Voidgel Orb', 'Tauforged Shard'
        ]
        
        for prime_item in items_list:
            prime_name = prime_item.get('name', '')
            if not prime_name or 'Prime' not in prime_name:
                continue
            
            if 'Galariak Prime' in prime_name or 'Sagek Prime' in prime_name:
                continue
            
            # Get all components for this Prime item
            components = prime_item.get('components', [])
            
            for component in components:
                component_unique_name = component.get('uniqueName', '')
                component_name = component.get('name', '')
                component_type = component.get('type', '')
                
                if not component_unique_name:
                    continue
                
                if component_type == 'Resource':
                    continue
                
                is_resource = any(keyword.lower() in component_name.lower() for keyword in resource_keywords)
                if is_resource:
                    continue
                
                component_name_lower = component_name.lower()
                is_valid_component = False
                
                for valid_type in valid_component_types:
                    valid_type_lower = valid_type.lower()
                    if (component_name_lower == valid_type_lower or 
                        component_name_lower.startswith(valid_type_lower + ' ') or
                        component_name_lower.endswith(' ' + valid_type_lower) or
                        ' ' + valid_type_lower + ' ' in ' ' + component_name_lower + ' '):
                        is_valid_component = True
                        break
                
                if not is_valid_component:
                    has_ducats = component.get('ducats', 0) > 0
                    has_prime_price = component.get('primeSellingPrice', 0) > 0
                    is_tradable = component.get('tradable', False)
                    if not (has_ducats or has_prime_price or is_tradable):
                        continue
                
                item_count = self.inventory_dict.get(component_unique_name, 0)
                
                if item_count == 0:
                    unique_name_parts = component_unique_name.split('/')
                    item_name_part = unique_name_parts[-1] if unique_name_parts else ""
                    
                    if item_name_part:
                        if "/Items/Warframes/" in component_unique_name or "/Types/Items/Warframes/" in component_unique_name:
                            recipe_path = component_unique_name.replace("/Items/Warframes/", "/Recipes/WarframeRecipes/")
                            recipe_path = recipe_path.replace("/Types/Items/Warframes/", "/Types/Recipes/WarframeRecipes/")
                            if recipe_path.endswith("Component"):
                                recipe_path = recipe_path.replace("Component", "Blueprint")
                            elif not recipe_path.endswith("Blueprint"):
                                recipe_path = recipe_path + "Blueprint"
                            item_count = self.inventory_dict.get(recipe_path, 0)
                        
                        if item_count == 0:
                            if item_name_part.endswith("Component"):
                                blueprint_name = item_name_part.replace("Component", "Blueprint")
                                recipe_path = f"/Lotus/Types/Recipes/WarframeRecipes/{blueprint_name}"
                                item_count = self.inventory_dict.get(recipe_path, 0)
                            else:
                                if not item_name_part.endswith("Blueprint"):
                                    recipe_path = f"/Lotus/Types/Recipes/WarframeRecipes/{item_name_part}Blueprint"
                                    item_count = self.inventory_dict.get(recipe_path, 0)
                                else:
                                    recipe_path = f"/Lotus/Types/Recipes/WarframeRecipes/{item_name_part}"
                                    item_count = self.inventory_dict.get(recipe_path, 0)
                        
                        if item_count == 0:
                            weapon_recipe_path = f"/Lotus/Types/Recipes/Weapons/{item_name_part}Blueprint"
                            item_count = self.inventory_dict.get(weapon_recipe_path, 0)
                            if item_count == 0:
                                weapon_recipe_path = f"/Lotus/Types/Recipes/Weapons/{item_name_part}"
                                item_count = self.inventory_dict.get(weapon_recipe_path, 0)
                        
                        if item_count == 0:
                            base_name = item_name_part
                            if base_name.endswith("Component"):
                                base_name = base_name.replace("Component", "")
                            elif base_name.endswith("Blueprint"):
                                base_name = base_name.replace("Blueprint", "")
                            
                            search_names = [base_name]
                            if "Helmet" in base_name:
                                neuroptics_name = base_name.replace("Helmet", "Neuroptics")
                                search_names.append(neuroptics_name)
                            
                            for inv_path, inv_count in self.inventory_dict.items():
                                if "/Recipes/" in inv_path:
                                    for search_name in search_names:
                                        if search_name in inv_path:
                                            if (inv_path.endswith(search_name + "Blueprint") or
                                                f"/{search_name}Blueprint" in inv_path):
                                                item_count = inv_count
                                                break
                                    if item_count > 0:
                                        break
                
                if item_count > 0:
                    full_item_name = f"{prime_name} {component_name}"
                    ducats = component.get('ducats', 0)
                    
                    prime_unique_name = prime_item.get('uniqueName', '')
                    category = getattr(self, 'item_category_map', {}).get(prime_unique_name, 'Unknown')
                    
                    if category == 'Unknown':
                        category = prime_item.get('category', 'Unknown')
                    
                    if category == 'Unknown':
                        slot = prime_item.get('slot', -1)
                        slot_to_category = {
                            0: 'Warframes',
                            1: 'Primary',
                            2: 'Secondary',
                            3: 'Melee',
                            4: 'Companions',
                            5: 'Archwing'
                        }
                        category = slot_to_category.get(slot, 'Unknown')
                    
                    inventory_items.append({
                        "name": full_item_name,
                        "amount": item_count,
                        "owned": False,
                        "cost": ducats,
                        "rarity": "Unknown",
                        "base_name": prime_name,
                        "component_type": component_name,
                        "category": category
                    })
        
        inventory_items.sort(key=lambda x: (x["base_name"], x["component_type"]))
        return inventory_items
    
    def setup_ui(self):
        main_container = tk.Frame(self.root, bg="#0f0f0f")
        main_container.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)
        
        top_bar = tk.Frame(main_container, bg="#1a1a2e", relief=tk.FLAT, bd=0)
        top_bar.pack(fill=tk.X, padx=0, pady=0)
        
        title_frame = tk.Frame(top_bar, bg="#1a1a2e")
        title_frame.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=15, pady=12)
        
        icon_path = os.path.join(self.cached_data_dir, "Ducat.png")
        if not os.path.exists(icon_path):
            icon_path = os.path.join(self.cached_data_dir, "ducat.png")
        
        if os.path.exists(icon_path) and PIL_AVAILABLE:
            try:
                pil_image = Image.open(icon_path)
                icon_image = ImageTk.PhotoImage(pil_image)
                self.root.iconphoto(True, icon_image)
                small_pil = pil_image.resize((pil_image.width // 5, pil_image.height // 5), Image.Resampling.LANCZOS)
                self.ducat_icon_small = ImageTk.PhotoImage(small_pil)
                icon_label = tk.Label(
                    title_frame,
                    image=self.ducat_icon_small,
                    bg="#1a1a2e"
                )
                icon_label.pack(side=tk.LEFT, padx=(0, 8))
                icon_label.image = self.ducat_icon_small
            except Exception as e:
                print(f"Failed to load icon: {e}")
        
        title_label = tk.Label(
            title_frame, 
            text="Ducanator", 
            font=("Segoe UI", 18, "bold"),
            bg="#1a1a2e",
            fg="#ffffff"
        )
        title_label.pack(side=tk.LEFT)
        
        stats_frame = tk.Frame(top_bar, bg="#1a1a2e")
        stats_frame.pack(side=tk.RIGHT, padx=15, pady=12)
        
        trade_container = tk.Frame(stats_frame, bg="#16213e", relief=tk.FLAT, bd=1)
        trade_container.pack(side=tk.LEFT, padx=5)
        
        tk.Label(
            trade_container,
            text="📦 FULL TRADES",
            font=("Segoe UI", 8),
            bg="#16213e",
            fg="#a0a0a0"
        ).pack(padx=12, pady=(8, 2))
        
        self.full_trade_label = tk.Label(
            trade_container,
            text="0",
            font=("Segoe UI", 16, "bold"),
            bg="#16213e",
            fg="#4ade80"
        )
        self.full_trade_label.pack(padx=12, pady=(0, 8))
        
        status_container = tk.Frame(stats_frame, bg="#16213e", relief=tk.FLAT, bd=1)
        status_container.pack(side=tk.LEFT, padx=5)
        
        tk.Label(
            status_container,
            text="📊 STATUS",
            font=("Segoe UI", 8),
            bg="#16213e",
            fg="#a0a0a0"
        ).pack(padx=12, pady=(8, 2))
        
        self.status_label = tk.Label(
            status_container,
            text="Ready",
            font=("Segoe UI", 10),
            bg="#16213e",
            fg="#4a9eff"
        )
        self.status_label.pack(padx=12, pady=(0, 8))
        
        control_panel = tk.Frame(main_container, bg="#16213e", relief=tk.FLAT)
        control_panel.pack(fill=tk.X, padx=0, pady=0)
        
        data_section = tk.LabelFrame(
            control_panel,
            text=" Data Management ",
            font=("Segoe UI", 9, "bold"),
            bg="#16213e",
            fg="#ffffff",
            relief=tk.FLAT,
            bd=0,
            labelanchor="nw"
        )
        data_section.pack(side=tk.LEFT, fill=tk.X, padx=10, pady=10, ipadx=5, ipady=5)
        
        refresh_btn = tk.Button(
            data_section,
            text="🔄 Reload JSON",
            command=lambda: self.load_inventory_from_json(run_api_helper_first=True),
            bg="#4a9eff",
            fg="white",
            font=("Segoe UI", 9, "bold"),
            padx=12,
            pady=6,
            relief=tk.FLAT,
            cursor="hand2",
            activebackground="#3a8eef",
            activeforeground="white"
        )
        refresh_btn.pack(side=tk.LEFT, padx=5)
        
        refresh_display_btn = tk.Button(
            data_section,
            text="↻ Refresh",
            command=self.refresh_display,
            bg="#5a5a6a",
            fg="white",
            font=("Segoe UI", 9),
            padx=12,
            pady=6,
            relief=tk.FLAT,
            cursor="hand2",
            activebackground="#4a4a5a",
            activeforeground="white"
        )
        refresh_display_btn.pack(side=tk.LEFT, padx=5)
        
        fetch_prices_btn = tk.Button(
            data_section,
            text="💰 Fetch Prices",
            command=self.manual_fetch_all_prices,
            bg="#f39c12",
            fg="white",
            font=("Segoe UI", 9),
            padx=12,
            pady=6,
            relief=tk.FLAT,
            cursor="hand2",
            activebackground="#e67e22",
            activeforeground="white"
        )
        fetch_prices_btn.pack(side=tk.LEFT, padx=5)
        
        marking_section = tk.LabelFrame(
            control_panel,
            text=" Item Marking ",
            font=("Segoe UI", 9, "bold"),
            bg="#16213e",
            fg="#ffffff",
            relief=tk.FLAT,
            bd=0,
            labelanchor="nw"
        )
        marking_section.pack(side=tk.LEFT, fill=tk.X, padx=10, pady=10, ipadx=5, ipady=5)
        
        toggle_marked_btn = tk.Button(
            marking_section,
            text="👁 Hide Marked",
            command=self.toggle_marked_items,
            bg="#9b59b6",
            fg="white",
            font=("Segoe UI", 9),
            padx=12,
            pady=6,
            relief=tk.FLAT,
            cursor="hand2",
            activebackground="#8b49a6",
            activeforeground="white"
        )
        toggle_marked_btn.pack(side=tk.LEFT, padx=5)
        self.toggle_marked_btn = toggle_marked_btn
        
        clear_marks_btn = tk.Button(
            marking_section,
            text="🗑 Clear All Marks",
            command=self.clear_all_marks,
            bg="#e74c3c",
            fg="white",
            font=("Segoe UI", 9),
            padx=12,
            pady=6,
            relief=tk.FLAT,
            cursor="hand2",
            activebackground="#d73c2c",
            activeforeground="white"
        )
        clear_marks_btn.pack(side=tk.LEFT, padx=5)
        
        filter_panel = tk.Frame(main_container, bg="#0f1419", relief=tk.FLAT)
        filter_panel.pack(fill=tk.X, padx=0, pady=0)
        
        search_row = tk.Frame(filter_panel, bg="#0f1419")
        search_row.pack(fill=tk.X, padx=15, pady=12)
        
        search_container = tk.Frame(search_row, bg="#1a2332", relief=tk.FLAT, bd=1)
        search_container.pack(side=tk.LEFT, padx=5, pady=5, fill=tk.X, expand=True)
        
        tk.Label(
            search_container,
            text="🔍 Search Items",
            font=("Segoe UI", 8, "bold"),
            bg="#1a2332",
            fg="#a0a0a0"
        ).pack(anchor=tk.W, padx=10, pady=(8, 2))
        
        search_input_frame = tk.Frame(search_container, bg="#1a2332")
        search_input_frame.pack(fill=tk.X, padx=10, pady=(0, 8))
        
        self.search_entry = tk.Entry(
            search_input_frame,
            font=("Segoe UI", 10),
            bg="#2a3441",
            fg="#ffffff",
            insertbackground="#ffffff",
            relief=tk.FLAT,
            bd=5
        )
        self.search_entry.pack(fill=tk.X, ipady=4)
        self.search_entry.bind("<KeyRelease>", self.on_search_change)
        
        ducat_container = tk.Frame(search_row, bg="#1a2332", relief=tk.FLAT, bd=1)
        ducat_container.pack(side=tk.LEFT, padx=5, pady=5, fill=tk.X)
        
        tk.Label(
            ducat_container,
            text="💰 Ducat Value",
            font=("Segoe UI", 8, "bold"),
            bg="#1a2332",
            fg="#a0a0a0"
        ).pack(anchor=tk.W, padx=10, pady=(8, 2))
        
        ducat_input_frame = tk.Frame(ducat_container, bg="#1a2332")
        ducat_input_frame.pack(fill=tk.X, padx=10, pady=(0, 8))
        
        self.ducat_entry = tk.Entry(
            ducat_input_frame,
            font=("Segoe UI", 10),
            bg="#2a3441",
            fg="#ffffff",
            insertbackground="#ffffff",
            relief=tk.FLAT,
            bd=5,
            width=10
        )
        self.ducat_entry.pack(fill=tk.X, ipady=4)
        self.ducat_entry.bind("<KeyRelease>", self.on_ducat_filter_change)
        
        platinum_container = tk.Frame(search_row, bg="#1a2332", relief=tk.FLAT, bd=1)
        platinum_container.pack(side=tk.LEFT, padx=5, pady=5, fill=tk.X)
        
        tk.Label(
            platinum_container,
            text="💎 Platinum Value",
            font=("Segoe UI", 8, "bold"),
            bg="#1a2332",
            fg="#a0a0a0"
        ).pack(anchor=tk.W, padx=10, pady=(8, 2))
        
        platinum_input_frame = tk.Frame(platinum_container, bg="#1a2332")
        platinum_input_frame.pack(fill=tk.X, padx=10, pady=(0, 8))
        
        self.platinum_entry = tk.Entry(
            platinum_input_frame,
            font=("Segoe UI", 10),
            bg="#2a3441",
            fg="#ffffff",
            insertbackground="#ffffff",
            relief=tk.FLAT,
            bd=5,
            width=10
        )
        self.platinum_entry.pack(fill=tk.X, ipady=4)
        self.platinum_entry.bind("<KeyRelease>", self.on_platinum_filter_change)
        
        clear_filters_btn = tk.Button(
            search_row,
            text="✕ Clear",
            command=self.clear_filters,
            bg="#5a5a6a",
            fg="white",
            font=("Segoe UI", 9),
            padx=15,
            pady=8,
            relief=tk.FLAT,
            cursor="hand2",
            activebackground="#4a4a5a",
            activeforeground="white"
        )
        clear_filters_btn.pack(side=tk.LEFT, padx=5, pady=5)
        
        category_section = tk.Frame(filter_panel, bg="#0f1419")
        category_section.pack(fill=tk.X, padx=15, pady=(0, 12))
        
        tk.Label(
            category_section,
            text="📁 Category Filter",
            font=("Segoe UI", 9, "bold"),
            bg="#0f1419",
            fg="#ffffff"
        ).pack(anchor=tk.W, pady=(0, 8))
        
        category_buttons_frame = tk.Frame(category_section, bg="#0f1419")
        category_buttons_frame.pack(fill=tk.X)
        
        self.category_buttons = {}
        categories = ["ALL", "Warframes", "Primary", "Secondary", "Melee", "Companions", "Archwing"]
        
        for category in categories:
            btn = tk.Button(
                category_buttons_frame,
                text=category,
                command=lambda c=category: self.select_category(c),
                bg="#2a3441",
                fg="#ffffff",
                font=("Segoe UI", 9),
                padx=15,
                pady=6,
                relief=tk.FLAT,
                cursor="hand2",
                activebackground="#3a4451",
                activeforeground="white"
            )
            btn.pack(side=tk.LEFT, padx=3)
            self.category_buttons[category] = btn
        
        self.category_buttons["ALL"].config(bg="#4a9eff", fg="white")
        
        content_frame = tk.Frame(main_container, bg="#0f0f0f")
        content_frame.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)
        
        content_wrapper = tk.Frame(content_frame, bg="#1a1a2e")
        content_wrapper.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        tree_frame = tk.Frame(content_wrapper, bg="#1a1a2e")
        tree_frame.pack(fill=tk.BOTH, expand=True)
        
        v_scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL)
        v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.tree = ttk.Treeview(
            tree_frame,
            columns=("Name", "Amount", "Ducats", "Platinum", "Status"),
            show="headings",
            yscrollcommand=v_scrollbar.set,
            selectmode="browse"
        )
        
        v_scrollbar.config(command=self.tree.yview)
        
        self.tree.heading("Name", text="Item Name")
        self.tree.heading("Amount", text="Quantity")
        self.tree.heading("Ducats", text="Ducats")
        self.tree.heading("Platinum", text="Platinum")
        self.tree.heading("Status", text="Status")
        
        self.tree.column("Name", width=200, anchor=tk.W, minwidth=150, stretch=True)
        self.tree.column("Amount", width=80, anchor=tk.CENTER, minwidth=70, stretch=False)
        self.tree.column("Ducats", width=80, anchor=tk.CENTER, minwidth=70, stretch=False)
        self.tree.column("Platinum", width=90, anchor=tk.CENTER, minwidth=80, stretch=False)
        self.tree.column("Status", width=100, anchor=tk.CENTER, minwidth=90, stretch=False)
        
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Treeview", 
                       background="#1e2749",
                       foreground="#ffffff",
                       fieldbackground="#1e2749",
                       rowheight=28,
                       borderwidth=0,
                       font=("Segoe UI", 9))
        style.configure("Treeview.Heading",
                       background="#16213e",
                       foreground="#ffffff",
                       relief=tk.FLAT,
                       borderwidth=0,
                       font=("Segoe UI", 9, "bold"),
                       padding=(5, 8))
        style.map("Treeview",
                 background=[("selected", "#4a9eff")],
                 foreground=[("selected", "white")])
        style.map("Treeview.Heading",
                 background=[("active", "#2a3441")],
                 foreground=[("active", "#4a9eff")])
        
        style.configure("Vertical.TScrollbar",
                       background="#16213e",
                       troughcolor="#0f1419",
                       borderwidth=0,
                       arrowcolor="#4a9eff",
                       darkcolor="#16213e",
                       lightcolor="#16213e",
                       width=12)
        style.map("Vertical.TScrollbar",
                 background=[("active", "#2a3441")],
                 arrowcolor=[("active", "#5aafff")],
                 slidercolor=[("active", "#4a9eff")])
        
        style.configure("TCombobox",
                       fieldbackground="#1a2332",
                       background="#1a2332",
                       foreground="#ffffff",
                       borderwidth=1,
                       relief=tk.SOLID,
                       arrowcolor="#4a9eff",
                       darkcolor="#1a2332",
                       lightcolor="#1a2332",
                       insertcolor="#ffffff")
        style.map("TCombobox",
                 fieldbackground=[("readonly", "#1a2332"), ("active", "#1a2332"), ("focus", "#1a2332")],
                 background=[("readonly", "#1a2332")],
                 foreground=[("readonly", "#ffffff")],
                 arrowcolor=[("active", "#5aafff"), ("!disabled", "#4a9eff")],
                 bordercolor=[("focus", "#3a4451"), ("!focus", "#3a4451")])
        
        def style_combobox_popup():
            def _find_and_style_listbox():
                try:
                    def get_all_children(parent):
                        children = []
                        try:
                            for child in parent.winfo_children():
                                children.append(child)
                                children.extend(get_all_children(child))
                        except:
                            pass
                        return children
                    
                    all_widgets = [self.root] + get_all_children(self.root)
                    
                    try:
                        all_widgets.extend([w for w in self.root.tk.eval('winfo children .').split() if w])
                    except:
                        pass
                    
                    for widget in all_widgets:
                        try:
                            if isinstance(widget, tk.Listbox):
                                widget.configure(
                                    bg="#2a3441",
                                    fg="#ffffff",
                                    selectbackground="#4a9eff",
                                    selectforeground="white",
                                    activestyle="none",
                                    relief=tk.FLAT,
                                    borderwidth=0,
                                    highlightthickness=0,
                                    font=("Segoe UI", 10)
                                )
                            elif isinstance(widget, tk.Toplevel):
                                try:
                                    widget.configure(bg="#2a3441")
                                except:
                                    pass
                                for child in get_all_children(widget):
                                    if isinstance(child, tk.Listbox):
                                        child.configure(
                                            bg="#2a3441",
                                            fg="#ffffff",
                                            selectbackground="#4a9eff",
                                            selectforeground="white",
                                            activestyle="none",
                                            relief=tk.FLAT,
                                            borderwidth=0,
                                            highlightthickness=0,
                                            font=("Segoe UI", 10)
                                        )
                        except:
                            continue
                except Exception:
                    pass
            
            for delay in [5, 15, 30, 50, 100, 200]:
                self.root.after(delay, _find_and_style_listbox)
        
        v_scrollbar.configure(style="Vertical.TScrollbar")
        
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        self.tree.bind("<Button-3>", self.on_item_click)
        self.tree.bind("<Double-Button-3>", self.on_item_click)
        
        def on_platinum_header_click(event):
            region = self.tree.identify_region(event.x, event.y)
            if region == "heading":
                column = self.tree.identify_column(event.x)
                if column == "#4":
                    self.toggle_platinum_sort()
                elif column == "#2":
                    self.toggle_amount_sort()
        
        self.tree.bind("<Button-1>", on_platinum_header_click)
    
    def on_search_change(self, event=None):
        self.search_text = self.search_entry.get().strip().lower()
        self.refresh_display()
    
    def on_ducat_filter_change(self, event=None):
        selected_value = self.ducat_entry.get().strip()
        self.ducat_filter = selected_value if selected_value else ""
        self.refresh_display()
    
    def on_platinum_filter_change(self, event=None):
        selected_value = self.platinum_entry.get().strip()
        old_filter = self.platinum_filter
        self.platinum_filter = selected_value if selected_value else ""
        
        try:
            filter_platinum = int(self.platinum_filter) if self.platinum_filter else None
            
            if not filter_platinum:
                for item_name in list(self.platinum_filter_marked):
                    if item_name in self.marked_items and not self._is_manually_marked(item_name):
                        self.marked_items.remove(item_name)
                self.platinum_filter_marked.clear()
                self.save_marked_items()
                self.refresh_display()
                return
            
            previously_filter_marked = self.platinum_filter_marked.copy()
            
            manually_marked_items = set()
            for item in self.inventory_data:
                item_name = item.get("name", "")
                if not item_name or item_name.startswith('---'):
                    continue
                
                base_name = item.get("base_name", "")
                if base_name:
                    base_marker = f"BASE:{base_name}"
                    if base_marker in self.marked_items:
                        manually_marked_items.add(item_name)
                        continue
                
                if item_name in self.marked_items and item_name not in previously_filter_marked:
                    manually_marked_items.add(item_name)
            
            self.platinum_filter_marked.clear()
            
            for item in self.inventory_data:
                item_name = item.get("name", "")
                if not item_name or item_name.startswith('---'):
                    continue
                
                if item_name in manually_marked_items:
                    continue
                
                platinum_price = None
                if item_name in self.price_cache:
                    cached = self.price_cache[item_name]
                    if isinstance(cached, dict) and cached.get('price') is not None:
                        platinum_price = cached.get('price')
                    elif isinstance(cached, (int, float)):
                        platinum_price = cached
                elif isinstance(self.price_cache.get(item_name), (int, float)):
                    platinum_price = self.price_cache[item_name]
                
                if platinum_price is None:
                    continue
                
                should_be_marked = platinum_price >= filter_platinum
                is_currently_marked = item_name in self.marked_items
                
                if should_be_marked:
                    if not is_currently_marked:
                        self.marked_items.add(item_name)
                        self.platinum_filter_marked.add(item_name)
                    elif item_name in previously_filter_marked:
                        self.platinum_filter_marked.add(item_name)
                else:
                    if is_currently_marked and item_name in previously_filter_marked:
                        self.marked_items.remove(item_name)
            
            if previously_filter_marked != self.platinum_filter_marked:
                self.save_marked_items()
            
        except ValueError:
            pass
        
        self.refresh_display()
    
    def _is_manually_marked(self, item_name):
        for inv_item in self.inventory_data:
            if inv_item.get("name") == item_name:
                base_name = inv_item.get("base_name", "")
                if base_name:
                    base_marker = f"BASE:{base_name}"
                    if base_marker in self.marked_items:
                        return True
                break
        
        if item_name in self.marked_items and item_name not in self.platinum_filter_marked:
            return True
        
        return False

    def toggle_amount_sort(self):
        self.amount_sort_state = (self.amount_sort_state + 1) % 3

        if self.amount_sort_state == 0:
            self.tree.heading("Amount", text="Quantity")
        elif self.amount_sort_state == 1:
            self.tree.heading("Amount", text="Quantity ↑")
        else:
            self.tree.heading("Amount", text="Quantity ↓")

        self.refresh_display()
    
    def toggle_platinum_sort(self):
        self.platinum_sort_state = (self.platinum_sort_state + 1) % 3
        if self.platinum_sort_state == 0:
            self.tree.heading("Platinum", text="Platinum")
        elif self.platinum_sort_state == 1:
            self.tree.heading("Platinum", text="Platinum ↑")
        else:
            self.tree.heading("Platinum", text="Platinum ↓")
        self.refresh_display()
    
    def select_category(self, category):
        self.selected_category = category
        
        for cat, btn in self.category_buttons.items():
            if cat == category:
                btn.config(bg="#4a9eff", fg="white")
            else:
                btn.config(bg="#2a3441", fg="#ffffff")
        
        self.refresh_display()
    
    def clear_filters(self):
        self.search_entry.delete(0, tk.END)
        self.ducat_entry.delete(0, tk.END)
        self.platinum_entry.delete(0, tk.END)
        self.search_text = ""
        self.ducat_filter = ""
        self.platinum_filter = ""
        self.platinum_sort_state = 0
        self.amount_sort_state = 0
        self.tree.heading("Platinum", text="Platinum")
        
        had_filter_marked = len(self.platinum_filter_marked) > 0
        for item_name in list(self.platinum_filter_marked):
            if item_name in self.marked_items and not self._is_manually_marked(item_name):
                self.marked_items.remove(item_name)
        self.platinum_filter_marked.clear()
        if had_filter_marked:
            self.save_marked_items()
        
        self.select_category("ALL")
        self.refresh_display()
    
    def calculate_full_trades(self, items):
        total_items = 0
        
        for item in items:
            item_id = item["name"]
            base_name = item.get("base_name", "")
            if self.is_item_marked(item_id, base_name):
                continue
            
            total_items += item.get("amount", 0)
        
        full_trades = total_items // 6
        return full_trades, total_items
    
    def update_full_trade_counter(self, filtered_items):
        full_trades, total_items = self.calculate_full_trades(filtered_items)
        self.full_trade_label.config(text=f"{full_trades} ({total_items} items)")
    
    def toggle_marked_items(self):
        self.show_marked = not self.show_marked
        if self.show_marked:
            self.toggle_marked_btn.config(text="Hide Marked")
        else:
            self.toggle_marked_btn.config(text="Show Marked")
        self.refresh_display()
    
    def refresh_display(self):
        primary_path = os.path.join(self.cached_data_dir, "Primary.json")
        inventory_path = os.path.join(self.cached_data_dir, "inventory.json")
        if not self.inventory_data and os.path.exists(primary_path) and os.path.exists(inventory_path):
            self.load_inventory_from_json()
        
        self._update_status_with_file_time()
        
        for item in self.tree.get_children():
            self.tree.delete(item)
        
        if not self.inventory_data:
            self.tree.insert("", tk.END, values=(
                "No data loaded",
                "Click 'Reload JSON' to load inventory",
                "",
                "",
                ""
            ))
            return
        
        filtered_items = []
        for item in self.inventory_data:
            item_id = item["name"]
            base_name = item.get("base_name", "")
            is_marked = self.is_item_marked(item_id, base_name)
            
            if self.selected_category != "ALL":
                item_category = item.get("category", "Unknown")
                if item_category != self.selected_category:
                    continue
            
            if not self.show_marked and is_marked:
                continue
            
            if self.search_text:
                if self.search_text not in item_id.lower():
                    continue
            
            if self.ducat_filter:
                try:
                    filter_ducats = int(self.ducat_filter)
                    item_ducats = item.get("cost", 0)
                    if item_ducats != filter_ducats:
                        continue
                except ValueError:
                    pass
            
            filtered_items.append(item)

        if self.amount_sort_state != 0:
            def get_amount(item):
                return item.get("amount", 0)

            if self.amount_sort_state == 1:
                filtered_items.sort(key=get_amount)
            else:
                filtered_items.sort(key=get_amount, reverse=True)

        
        if self.platinum_sort_state != 0:
            def get_platinum_price(item):
                item_name = item.get("name", "")
                if item_name in self.price_cache:
                    cached = self.price_cache[item_name]
                    if isinstance(cached, dict) and cached.get('price') is not None:
                        return cached.get('price', 0)
                    elif isinstance(cached, (int, float)):
                        return cached
                elif isinstance(self.price_cache.get(item_name), (int, float)):
                    return self.price_cache[item_name]
                return 0
            
            if self.platinum_sort_state == 1:
                filtered_items.sort(key=get_platinum_price)
            else:
                filtered_items.sort(key=get_platinum_price, reverse=True)
        
        current_base = None
        for item in filtered_items:
            item_id = item["name"]
            base_name = item.get("base_name", "")
            is_marked = self.is_item_marked(item_id, base_name)
            status = "✗ MARKED" if is_marked else ""
            
            if base_name and base_name != current_base:
                current_base = base_name
                base_marker = f"BASE:{base_name}"
                base_is_marked = base_marker in self.marked_items
                separator_status = "✗ MARKED" if base_is_marked else ""
                separator_tags = ("separator", "marked") if base_is_marked else ("separator",)
                self.tree.insert("", tk.END, 
                               values=(f"--- {base_name} ---", "", "", "", separator_status),
                               tags=separator_tags)
            
            tags = ("marked",) if is_marked else ("normal",)
            
            ducats = item.get("cost", 0)
            display_value = str(ducats) if ducats > 0 else ""
            
            item_name = item["name"]
            platinum_price = ""
            if item_name in self.price_cache:
                cached = self.price_cache[item_name]
                if isinstance(cached, dict) and cached.get('price') is not None:
                    platinum_price = str(cached['price'])
                elif isinstance(cached, (int, float)):
                    platinum_price = str(cached)
            elif isinstance(self.price_cache.get(item_name), (int, float)):
                platinum_price = str(self.price_cache[item_name])
            
            self.tree.insert("", tk.END, 
                           values=(
                               item["name"],
                               f"{item['amount']}",
                               display_value,
                               platinum_price,
                               status
                           ),
                           tags=tags)
        
        self.tree.tag_configure("marked", background="#2a1f1f", foreground="#ff6b6b")
        self.tree.tag_configure("normal", background="#1e2749", foreground="#ffffff")
        self.tree.tag_configure("separator", background="#16213e", foreground="#4a9eff", font=("Segoe UI", 9, "bold"))
        
        self.update_full_trade_counter(filtered_items)
    
    def is_item_marked(self, item_name, base_name=None):
        if item_name in self.marked_items:
            return True
        
        if base_name:
            base_marker = f"BASE:{base_name}"
            if base_marker in self.marked_items:
                return True
        
        return False
    
    def on_item_click(self, event):
        item = self.tree.identify_row(event.y)
        if not item:
            return
        
        self.tree.selection_set(item)
        
        values = self.tree.item(item, "values")
        tags = self.tree.item(item, "tags")
        
        if values:
            item_name = values[0]
            
            if "separator" in tags or item_name.startswith("---"):
                base_name = item_name.replace("---", "").strip()
                base_marker = f"BASE:{base_name}"
                
                if base_marker in self.marked_items:
                    self.marked_items.remove(base_marker)
                    items_to_remove = [name for name in self.marked_items 
                                     if name.startswith(base_name + " ")]
                    for name in items_to_remove:
                        self.marked_items.remove(name)
                else:
                    self.marked_items.add(base_marker)
                    for inv_item in self.inventory_data:
                        if inv_item.get("base_name") == base_name:
                            component_name = inv_item.get("name")
                            if component_name:
                                self.marked_items.add(component_name)
                
                self.save_marked_items()
                self.refresh_display()
                return
            
            base_name = None
            for inv_item in self.inventory_data:
                if inv_item.get("name") == item_name:
                    base_name = inv_item.get("base_name")
                    break
            
            if item_name in self.marked_items:
                self.marked_items.remove(item_name)
            else:
                self.marked_items.add(item_name)
            
            self.save_marked_items()
            self.refresh_display()
    
    def clear_all_marks(self):
        self.marked_items.clear()
        self.save_marked_items()
        self.refresh_display()

def main():
    root = tk.Tk()
    app = Ducanator(root)
    root.mainloop()

if __name__ == "__main__":
    main()

