/* ============================================================================
 *  CERTEUS — File List (mini viewer navigator)
 *  PL: Prosta lista plików (miniatura + tytuł), klikalna, z podświetleniem.
 *      Monochromatycznie, bez zależności. Exports: window.CerteusFileList.
 *  EN: Simple clickable file list (thumb + title), with selection highlight.
 *      Monochrome, zero deps. Exports: window.CerteusFileList.
 * ----------------------------------------------------------------------------
 *  API (public):
 *    render(container, items, opts?)
 *      - container: HTMLElement|string (selector)
 *      - items: [{ id, name, url, kind, meta? }]
 *          kind ∈ {"pdf","image","text","other"} (affects icon)
 *      - opts:
 *          onSelect(id, item)   // called when user clicks an item
 *          activeId             // preselected id
 *          lang: "pl"|"en"      // optional; auto from <html lang="...">
 *          compact: boolean     // tighter paddings
 *          enableToggleKeyM: true|false  // press 'M' to collapse/expand
 *    setItems(items)            // rerender with new items
 *    setActive(id)              // highlight by id
 *    collapse()/expand()/toggle()
 *  Notes:
 *    - Lines ≤ 100 chars, LF EOL, no trailing spaces.
 * ==========================================================================*/

(() => {
    "use strict";

    const I18N = {
        pl: {
            header: "Pliki",
            empty: "Brak plików",
            toggle: "Pokaż/ukryj listę (M)",
        },
        en: {
            header: "Files",
            empty: "No files",
            toggle: "Show/hide list (M)",
        },
    };

    function getLang() {
        const lang = (document.documentElement.lang || "pl").toLowerCase();
        return lang.startsWith("en") ? "en" : "pl";
    }

    function el(tag, props = {}, children = []) {
        const n = document.createElement(tag);
        Object.entries(props).forEach(([k, v]) => {
            if (k === "class") n.className = String(v || "");
            else if (k === "for") n.htmlFor = String(v || "");
            else if (k in n) n[k] = v;
            else n.setAttribute(k, String(v));
        });
        [].concat(children).forEach((c) => {
            if (c == null) return;
            n.appendChild(
                typeof c === "string" ? document.createTextNode(c) : c,
            );
        });
        return n;
    }

    function icon(kind) {
        // PL/EN: simple mono icons via emojis (no external assets)
        if (kind === "pdf") return "📄";
        if (kind === "image") return "🖼️";
        if (kind === "text") return "📝";
        return "📦";
    }

    function sanitize(s, fallback = "") {
        return typeof s === "string" ? s : fallback;
    }

    let _state = {
        root: null,
        listEl: null,
        items: [],
        activeId: null,
        lang: getLang(),
        collapsed: false,
        opts: {},
    };

    function _buildHeader(T) {
        const btn = el(
            "button",
            {
                type: "button",
                title: T.toggle,
                class: "cf-list-toggle",
                style:
                    "border:1px solid currentColor;background:transparent;padding:.25rem .5rem;" +
                    "cursor:pointer;border-radius:.5rem;",
            },
            T.header,
        );
        btn.addEventListener("click", toggle);
        return el(
            "div",
            {
                class: "cf-list-head",
                style:
                    "display:flex;align-items:center;justify-content:space-between;" +
                    "gap:.5rem;margin-bottom:.5rem;",
            },
            [el("div", {}, T.header), btn],
        );
    }

    function _buildItem(it, active) {
        const pad = _state.opts.compact ? ".25rem .5rem" : ".5rem .75rem";
        const li = el(
            "button",
            {
                type: "button",
                class: "cf-item",
                style:
                    "width:100%;text-align:left;border:1px solid currentColor;" +
                    `padding:${pad};margin-bottom:.25rem;display:flex;align-items:center;gap:.5rem;` +
                    "background:transparent;border-radius:.5rem;cursor:pointer;" +
                    (active
                        ? "outline:2px solid currentColor;"
                        : "outline:none;"),
            },
            [
                el("span", { "aria-hidden": "true" }, icon(it.kind)),
                el("span", {}, sanitize(it.name, it.id)),
            ],
        );
        li.addEventListener("click", () => {
            setActive(it.id);
            if (typeof _state.opts.onSelect === "function")
                _state.opts.onSelect(it.id, it);
        });
        li.dataset.id = it.id;
        return li;
    }

    function _renderList() {
        if (!_state.root) return;
        const T = I18N[_state.lang] || I18N.pl;

        _state.root.innerHTML = "";
        const boxPad = _state.opts.compact ? ".5rem" : ".75rem";
        const box = el(
            "div",
            {
                class: "cf-box",
                style:
                    "border:1px solid currentColor;border-radius:.75rem;padding:" +
                    boxPad +
                    ";display:grid;gap:.25rem;",
            },
            [],
        );

        box.appendChild(_buildHeader(T));

        const list = el(
            "div",
            {
                class: "cf-list",
                style:
                    (_state.collapsed ? "display:none;" : "display:block;") +
                    "max-height:240px;overflow:auto;",
            },
            [],
        );
        _state.listEl = list;

        if (!_state.items.length) {
            list.appendChild(
                el("div", { class: "cf-empty", style: "opacity:.7;" }, T.empty),
            );
        } else {
            _state.items.forEach((it) => {
                list.appendChild(_buildItem(it, it.id === _state.activeId));
            });
        }

        box.appendChild(list);
        _state.root.appendChild(box);
    }

    function setItems(items) {
        _state.items = Array.isArray(items) ? items.slice() : [];
        if (
            _state.activeId &&
            !_state.items.find((x) => x.id === _state.activeId)
        ) {
            _state.activeId = null;
        }
        _renderList();
    }

    function setActive(id) {
        _state.activeId = id || null;
        if (_state.listEl) {
            _state.listEl.querySelectorAll(".cf-item").forEach((node) => {
                const isActive = node.dataset.id === _state.activeId;
                node.style.outline = isActive
                    ? "2px solid currentColor"
                    : "none";
            });
        }
    }

    function collapse() {
        _state.collapsed = true;
        _renderList();
    }
    function expand() {
        _state.collapsed = false;
        _renderList();
    }
    function toggle() {
        _state.collapsed = !_state.collapsed;
        _renderList();
    }

    function _bindKeyM() {
        if (_state.opts.enableToggleKeyM === false) return;
        window.addEventListener("keydown", (e) => {
            if ((e.key || "").toLowerCase() === "m") toggle();
        });
    }

    function render(container, items, opts = {}) {
        const root =
            typeof container === "string"
                ? document.querySelector(container)
                : container;
        if (!root) return;
        _state.root = root;
        _state.lang = opts.lang || getLang();
        _state.opts = opts || {};
        _state.activeId = opts.activeId || null;
        _bindKeyM();
        setItems(items || []);
    }

    window.CerteusFileList = {
        render,
        setItems,
        setActive,
        collapse,
        expand,
        toggle,
    };
})();
