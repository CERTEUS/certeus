/* ============================================================================
 *  CERTEUS — Case Manager (UI helper)
 *  PL: Prosty selektor spraw + pamięć ostatnich (localStorage).
 *  EN: Simple case picker + recent cases memory (localStorage).
 * ----------------------------------------------------------------------------
 *  Zasady / Rules:
 *   - Monochromatycznie (brak własnych kolorów, dziedziczy motyw strony).
 *   - Brak zależności; czysty JS.
 *   - Maks. 10 ostatnich spraw; deduplikacja po `id`.
 *   - I18N: PL/EN (auto wg `lang`, fallback "pl").
 *   - Linie ≤ 100 znaków.
 * ==========================================================================*/

(() => {
    "use strict";

    /** PL: Klucze LS. EN: LocalStorage keys. */
    const LS_KEYS = {
        recent: "certeus:recent_cases",
        active: "certeus:active_case",
    };

    /** PL: Maks. liczba zapamiętanych spraw. EN: Max number of stored recents. */
    const MAX_RECENTS = 10;

    /** PL/EN: Minimal i18n. */
    const I18N = {
        pl: {
            pickerLabel: "Sprawa",
            newCase: "Nowa sprawa…",
            placeholderId: "ID sprawy",
            placeholderTitle: "Tytuł (opcjonalnie)",
            btnAdd: "Dodaj",
            none: "Brak",
        },
        en: {
            pickerLabel: "Case",
            newCase: "New case…",
            placeholderId: "Case ID",
            placeholderTitle: "Title (optional)",
            btnAdd: "Add",
            none: "None",
        },
    };

    /** PL: Odczyt języka z `document.documentElement.lang`. EN: Read page lang. */
    function getLang() {
        const lang = (document.documentElement.lang || "pl").toLowerCase();
        return lang.startsWith("en") ? "en" : "pl";
    }

    /** PL/EN: Safe JSON parse. */
    function safeParse(str, fallback) {
        try {
            return JSON.parse(str);
        } catch {
            return fallback;
        }
    }

    /** PL/EN: Read recent cases array. */
    function readRecents() {
        const raw = localStorage.getItem(LS_KEYS.recent);
        const arr = safeParse(raw || "[]", []);
        return Array.isArray(arr) ? arr : [];
    }

    /** PL/EN: Write recent cases array. */
    function writeRecents(arr) {
        localStorage.setItem(LS_KEYS.recent, JSON.stringify(arr));
    }

    /** PL/EN: Get active case id. */
    function getActiveCase() {
        return localStorage.getItem(LS_KEYS.active) || "";
    }

    /** PL/EN: Set active case id. */
    function setActiveCase(id) {
        if (typeof id === "string") localStorage.setItem(LS_KEYS.active, id);
    }

    /** PL/EN: Add or refresh a case (id, title?), keep MAX_RECENTS, de-dup by id. */
    function addCase(id, title) {
        if (!id || typeof id !== "string") return;
        const now = Date.now();
        const recents = readRecents().filter((x) => x && x.id);
        const without = recents.filter((x) => x.id !== id);
        const next = [{ id, title: title || "", ts: now }, ...without].slice(
            0,
            MAX_RECENTS,
        );
        writeRecents(next);
        setActiveCase(id);
    }

    /** PL/EN: List recent cases (sorted by ts desc). */
    function listCases() {
        const arr = readRecents().filter((x) => x && x.id);
        return arr.sort((a, b) => (b.ts || 0) - (a.ts || 0));
    }

    /** PL/EN: Helper to create element. */
    function el(tag, props = {}, children = []) {
        const node = document.createElement(tag);
        Object.entries(props).forEach(([k, v]) => {
            if (k === "class") node.className = String(v || "");
            else if (k === "for") node.htmlFor = String(v || "");
            else if (k in node) node[k] = v;
            else node.setAttribute(k, String(v));
        });
        [].concat(children).forEach((c) => {
            if (c == null) return;
            if (typeof c === "string")
                node.appendChild(document.createTextNode(c));
            else node.appendChild(c);
        });
        return node;
    }

    /**
     * PL: Renderuje selektor spraw do `container` i rejestruje zdarzenia.
     * EN: Renders case picker into `container` and wires events.
     *
     * @param {HTMLElement|string} container - element lub selektor CSS
     * @param {Object} opts
     *  - onChange(id): callback przy zmianie aktywnej sprawy
     *  - showNewForm: bool, czy pokazać formularz "Nowa sprawa…"
     */
    function renderCasePicker(container, opts = {}) {
        const lang = getLang();
        const T = I18N[lang];

        const root =
            typeof container === "string"
                ? document.querySelector(container)
                : container;
        if (!root) return;

        // Wrapper (monochromatyczny, dziedziczy style)
        const wrap = el("div", {
            class: "certeus-case-picker",
            style: "display:grid;gap:.5rem",
        });

        const label = el(
            "label",
            { for: "certeus-case-select" },
            T.pickerLabel,
        );
        const select = el("select", { id: "certeus-case-select" });

        // Opcje: None + recent cases
        select.appendChild(el("option", { value: "" }, `— ${T.none} —`));
        listCases().forEach((c) => {
            const optTitle = c.title ? `${c.id} — ${c.title}` : c.id;
            const opt = el("option", { value: c.id }, optTitle);
            select.appendChild(opt);
        });

        // Ustaw aktywną
        const active = getActiveCase();
        if (active) select.value = active;

        // Zmiana aktywnej sprawy
        select.addEventListener("change", () => {
            setActiveCase(select.value);
            if (typeof opts.onChange === "function")
                opts.onChange(select.value);
        });

        wrap.appendChild(label);
        wrap.appendChild(select);

        // Formularz "Nowa sprawa…" (opcjonalnie)
        if (opts.showNewForm !== false) {
            const form = el("div", {
                class: "certeus-new-case",
                style: "display:grid;gap:.25rem",
            });
            const heading = el(
                "div",
                { class: "certeus-new-heading" },
                T.newCase,
            );
            const idInput = el("input", {
                type: "text",
                placeholder: T.placeholderId,
                id: "certeus-new-id",
                autocomplete: "off",
            });
            const titleInput = el("input", {
                type: "text",
                placeholder: T.placeholderTitle,
                id: "certeus-new-title",
                autocomplete: "off",
            });
            const addBtn = el(
                "button",
                { type: "button", id: "certeus-new-add" },
                T.btnAdd,
            );

            addBtn.addEventListener("click", () => {
                const id = idInput.value.trim();
                const title = titleInput.value.trim();
                if (!id) return;
                addCase(id, title);
                // Re-render select
                while (select.firstChild) select.removeChild(select.firstChild);
                select.appendChild(
                    el("option", { value: "" }, `— ${T.none} —`),
                );
                listCases().forEach((c) => {
                    const t = c.title ? `${c.id} — ${c.title}` : c.id;
                    select.appendChild(el("option", { value: c.id }, t));
                });
                select.value = id;
                if (typeof opts.onChange === "function") opts.onChange(id);
                idInput.value = "";
                titleInput.value = "";
            });

            form.appendChild(heading);
            form.appendChild(idInput);
            form.appendChild(titleInput);
            form.appendChild(addBtn);
            wrap.appendChild(form);
        }

        root.innerHTML = "";
        root.appendChild(wrap);
    }

    // Eksport prostego API do `window.CerteusCaseManager`
    window.CerteusCaseManager = {
        addCase,
        listCases,
        getActiveCase,
        setActiveCase,
        renderCasePicker,
    };
})();
