/* ============================================================================
 *  CERTEUS — File List Bridge (uploads ↔ viewer)
 *  PL: Spina dropzone/uploady z mini listą i viewerem (+ prev/next).
 *  EN: Bridges uploads to mini file list and viewer (+ prev/next).
 *  Zasady: mono UI, brak zależności, linie ≤ 100 znaków.
 * ==========================================================================*/

(() => {
  "use strict";

  const S = {
    listSel: "#file-list",
    prevBtn: "#prevFile",
    nextBtn: "#nextFile",
    indicator: "#fileIndicator",
    viewerSel:
      "#previewFrame, #viewerFrame, #previewObject, #viewerObject, " +
      "#previewImage, #viewerImage, #viewerEmbed",
  };

  const state = {
    items: [],        // [{id,name,url,kind,meta}]
    idx: -1,          // aktywny indeks
  };

  function _viewerEl() {
    return document.querySelector(S.viewerSel);
  }

  function _kindFromType(ct) {
    const t = String(ct || "").toLowerCase();
    if (t === "application/pdf") return "pdf";
    if (t.startsWith("image/")) return "image";
    if (t.startsWith("text/")) return "text";
    return "other";
  }

  function _applyToViewer(url) {
    const v = _viewerEl();
    if (!v || !url) return;
    if (v.tagName === "IMG") v.src = url;
    else if ("data" in v) v.data = url;  // <object>
    else v.src = url;                    // <iframe>/<embed>
  }

  function _updateIndicator() {
    const el = document.querySelector(S.indicator);
    if (!el) return;
    const total = state.items.length;
    const pos = state.idx >= 0 ? state.idx + 1 : 0;
    el.textContent = `${pos}/${total}`;
  }

  function _refreshList(renderActiveOnly) {
    if (!window.CerteusFileList) return;
    window.CerteusFileList.setItems(state.items);
    if (state.idx >= 0 && state.items[state.idx]) {
      const id = state.items[state.idx].id;
      window.CerteusFileList.setActive(id);
      if (!renderActiveOnly) _applyToViewer(state.items[state.idx].url);
    }
    _updateIndicator();
  }

  function setItems(arr) {
    state.items = Array.isArray(arr) ? arr.slice() : [];
    state.idx = state.items.length ? 0 : -1;
    if (window.CerteusFileList) {
      window.CerteusFileList.render(S.listSel, state.items, {
        activeId: state.items[0]?.id || null,
        onSelect: (id, it) => {
          const i = state.items.findIndex((x) => x.id === id);
          if (i >= 0) {
            state.idx = i;
            _applyToViewer(state.items[i].url);
            _updateIndicator();
          } else if (it?.url) {
            _applyToViewer(it.url);
          }
        },
        enableToggleKeyM: true,
      });
    }
    if (state.idx >= 0) _applyToViewer(state.items[state.idx].url);
    _updateIndicator();
  }

  function addFile(obj) {
    // obj: {id,name,url,type|kind,meta?}
    if (!obj) return;
    const id = String(obj.id ?? (Date.now() + "-" + Math.random().toString(36).slice(2)));
    const name = obj.name || "plik";
    const url = obj.url || "";
    const kind = obj.kind || _kindFromType(obj.type);
    const meta = obj.meta || {};
    const item = { id, name, url, kind, meta };

    // deduplikacja po id
    const without = state.items.filter((x) => x.id !== id);
    state.items = [...without, item];
    // jeśli nic nieaktywne — ustaw pierwszy
    if (state.idx < 0) state.idx = 0;
    _refreshList(false);
    return item;
  }

  function removeFile(id) {
    if (!id) return;
    const i = state.items.findIndex((x) => x.id === id);
    if (i < 0) return;
    state.items.splice(i, 1);
    if (state.items.length === 0) state.idx = -1;
    else if (state.idx >= state.items.length) state.idx = state.items.length - 1;
    _refreshList(true);
  }

  function selectIndex(i) {
    if (i < 0 || i >= state.items.length) return;
    state.idx = i;
    _refreshList(false);
  }

  function next() {
    if (!state.items.length) return;
    state.idx = (state.idx + 1) % state.items.length;
    _refreshList(false);
  }

  function prev() {
    if (!state.items.length) return;
    state.idx = (state.idx - 1 + state.items.length) % state.items.length;
    _refreshList(false);
  }

  function bindNav() {
    const prevBtn = document.querySelector(S.prevBtn);
    const nextBtn = document.querySelector(S.nextBtn);
    prevBtn && prevBtn.addEventListener("click", prev);
    nextBtn && nextBtn.addEventListener("click", next);
  }

  // Auto-bind na DOMContentLoaded
  document.addEventListener("DOMContentLoaded", bindNav);

  // Eksport prostego API
  window.CerteusFileBridge = {
    setItems, addFile, removeFile, selectIndex, next, prev,
  };
})();
